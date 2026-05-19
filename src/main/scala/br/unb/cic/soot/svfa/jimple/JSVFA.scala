package br.unb.cic.soot.svfa.jimple

import java.util
import br.unb.cic.soot.svfa.jimple.rules.RuleAction
import br.unb.cic.soot.graph.{CallSiteCloseLabel, CallSiteLabel, CallSiteOpenLabel, ContextSensitiveRegion, GraphNode, SimpleNode, SinkNode, SourceNode, StatementNode, VisitedMethods}
import br.unb.cic.soot.svfa.jimple.dsl.{DSL, LanguageParser}
import br.unb.cic.soot.svfa.{SVFA, SourceSinkDef}
import com.typesafe.scalalogging.LazyLogging
import soot.jimple._
import soot.jimple.internal.{JArrayRef, JAssignStmt, JInstanceFieldRef}
import soot.jimple.spark.ondemand.DemandCSPointsTo
import soot.jimple.spark.pag
import soot.jimple.spark.pag.{AllocNode, PAG}
import soot.jimple.spark.sets.{DoublePointsToSet, HybridPointsToSet, PointsToSetInternal, P2SetVisitor}
import soot.toolkits.graph.ExceptionalUnitGraph
import soot.toolkits.scalar.SimpleLocalDefs
import soot.jimple.toolkits.callgraph.Edge
import soot.{ArrayType, FastHierarchy, Local, PointsToSet, RefType, Scene, SceneTransformer, SootField, SootMethod, Transform, Value, jimple}
import scala.collection.JavaConverters._
import scala.collection.mutable.ListBuffer

/**
 * A Jimple based implementation of
 * SVFA.
 */
abstract class JSVFA extends SVFA with Analysis with AnalysisDepth with FieldSensitiveness with ObjectPropagation with SourceSinkDef with LazyLogging with DSL {

  val visitedMethodsDepth = new ListBuffer[SootMethod]()
  val visitedMethodsAllocationSites = scala.collection.mutable.Set.empty[SootMethod]
  var numberVisitedMethods = 0
  var printDepthVisitedMethods: Boolean = false
  var methods = 0
  val traversedMethods = scala.collection.mutable.Set.empty[SootMethod]
  val storedFields = scala.collection.mutable.Set.empty[SootField]
  val allocationSites = scala.collection.mutable.HashMap.empty[soot.Value, StatementNode]
  val arrayStores = scala.collection.mutable.HashMap.empty[Local, List[soot.Unit]]
  val languageParser = new LanguageParser(this)
  val methodRules = languageParser.evaluate(code())
  var countNoEdges: Int = 0
  var countWithEdges: Int = 0

  /*
   * Create an edge  from the definition of the local argument
   * to the definitions of the base object of a method call. In
   * more details, we should use this rule to address a situation
   * like:
   *
   * - virtualinvoke r3.<java.lang.StringBuffer: java.lang.StringBuffer append(java.lang.String)>(r1);
   *
   * Where we wanto create an edge from the definitions of r1 to
   * the definitions of r3.
   */
  trait CopyFromMethodArgumentToBaseObject extends RuleAction {
    def from: Int

    def apply(sootMethod: SootMethod, invokeStmt: jimple.Stmt, localDefs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
      var srcArg: Value = null
      var expr: InvokeExpr = null

      try {
        srcArg = invokeStmt.getInvokeExpr.getArg(from)
        expr = invokeStmt.getInvokeExpr
      } catch {
        case e: Exception =>
          println("An error occurred in getInvokeExpr with args: " + invokeStmt.getInvokeExpr + " -> " + e)
      }
      if (hasBaseObject(expr) && srcArg.isInstanceOf[Local]) {
        val local = srcArg.asInstanceOf[Local]

        val base = getBaseObject(expr)

        if (base.isInstanceOf[Local]) {
          val localBase = base.asInstanceOf[Local]
          localDefs.getDefsOfAt(local, invokeStmt).forEach(sourceStmt => {
            val sourceNode = createNode(sootMethod, sourceStmt, visitedMethods)
            localDefs.getDefsOfAt(localBase, invokeStmt).forEach(targetStmt => {
              val targetNode = createNode(sootMethod, targetStmt, visitedMethods)
              updateGraph(sourceNode, targetNode)
            })
          })
        }
      }
    }
  }

  private def getBaseObject(expr: InvokeExpr) =
    if (expr.isInstanceOf[VirtualInvokeExpr])
      expr.asInstanceOf[VirtualInvokeExpr].getBase
    else if (expr.isInstanceOf[SpecialInvokeExpr])
      expr.asInstanceOf[SpecialInvokeExpr].getBase
    else
      expr.asInstanceOf[InstanceInvokeExpr].getBase


  private def hasBaseObject(expr: InvokeExpr) =
    (expr.isInstanceOf[VirtualInvokeExpr] || expr.isInstanceOf[SpecialInvokeExpr] || expr.isInstanceOf[InterfaceInvokeExpr])


  /*
     * Create an edge from a method call to a local.
     * In more details, we should use this rule to address
     * a situation like:
     *
     * - $r6 = virtualinvoke r3.<java.lang.StringBuffer: java.lang.String toString()>();
     *
     * Where we want to create an edge from the definitions of r3 to
     * this statement.
     */
  trait CopyFromMethodCallToLocal extends RuleAction {
    def apply(sootMethod: SootMethod, invokeStmt: jimple.Stmt, localDefs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
      val expr = invokeStmt.getInvokeExpr
      if (hasBaseObject(expr) && invokeStmt.isInstanceOf[jimple.AssignStmt]) {
        val base = getBaseObject(expr)
        val local = invokeStmt.asInstanceOf[jimple.AssignStmt].getLeftOp
        if (base.isInstanceOf[Local] && local.isInstanceOf[Local]) {
          val localBase = base.asInstanceOf[Local]
          localDefs.getDefsOfAt(localBase, invokeStmt).forEach(source => {
            val sourceNode = createNode(sootMethod, source, visitedMethods)
            val targetNode = createNode(sootMethod, invokeStmt, visitedMethods)
            updateGraph(sourceNode, targetNode)
          })
        }
      }
    }
  }


  /* Create an edge from the definitions of a local argument
   * to the assignment statement. In more details, we should use this rule to address
   * a situation like:
   * $r12 = virtualinvoke $r11.<java.lang.StringBuilder: java.lang.StringBuilder append(java.lang.String)>(r6);
   */
  trait CopyFromMethodArgumentToLocal extends RuleAction {
    def from: Int

    def apply(sootMethod: SootMethod, invokeStmt: jimple.Stmt, localDefs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
      val srcArg = invokeStmt.getInvokeExpr.getArg(from)
      if (invokeStmt.isInstanceOf[JAssignStmt] && srcArg.isInstanceOf[Local]) {
        val local = srcArg.asInstanceOf[Local]
        val targetStmt = invokeStmt.asInstanceOf[jimple.AssignStmt]
        localDefs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
          val source = createNode(sootMethod, sourceStmt, visitedMethods)
          val target = createNode(sootMethod, targetStmt, visitedMethods)
          updateGraph(source, target)
        })
      }
    }
  }

  /*
 * Create an edge between the definitions of the actual
 * arguments of a method call. We should use this rule
 * to address situations like:
 *
 * - System.arraycopy(l1, _, l2, _)
 *
 * Where we wanto to create an edge from the definitions of
 * l1 to the definitions of l2.
 */
  trait CopyBetweenArgs extends RuleAction {
    def from: Int

    def target: Int

    def apply(sootMethod: SootMethod, invokeStmt: jimple.Stmt, localDefs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
      val srcArg = invokeStmt.getInvokeExpr.getArg(from)
      val destArg = invokeStmt.getInvokeExpr.getArg(target)
      if (srcArg.isInstanceOf[Local] && destArg.isInstanceOf[Local]) {
        localDefs.getDefsOfAt(srcArg.asInstanceOf[Local], invokeStmt).forEach(sourceStmt => {
          val sourceNode = createNode(sootMethod, sourceStmt, visitedMethods)
          localDefs.getDefsOfAt(destArg.asInstanceOf[Local], invokeStmt).forEach(targetStmt => {
            val targetNode = createNode(sootMethod, targetStmt, visitedMethods)
            updateGraph(sourceNode, targetNode)
          })
        })
      }
    }
  }

  def createSceneTransform(): (String, Transform) = ("wjtp", new Transform("wjtp.svfa", new Transformer()))

  def initAllocationSites(): Unit = {
    val listener = Scene.v().getReachableMethods.listener()

    while (listener.hasNext) {
      val m = listener.next().method()

      updateAllocationSites(m, new ListBuffer[VisitedMethods]())

    }
  }

  def updateAllocationSites(m: SootMethod, visitedMethods: ListBuffer[VisitedMethods]): Unit = {

    if (visitedMethodsAllocationSites.contains(m)) {
      return
    }

    visitedMethodsAllocationSites.add(m)

    if (m.hasActiveBody) {
      val body = m.getActiveBody
      body.getUnits.forEach(unit => {
        if (unit.isInstanceOf[soot.jimple.AssignStmt]) {
          val left = unit.asInstanceOf[soot.jimple.AssignStmt].getLeftOp
          if (left.isInstanceOf[InstanceFieldRef]) {
            storedFields.add(left.asInstanceOf[InstanceFieldRef].getField)
          } else if (left.isInstanceOf[StaticFieldRef]) {
            storedFields.add(left.asInstanceOf[StaticFieldRef].getField)
          }

          val right = unit.asInstanceOf[soot.jimple.AssignStmt].getRightOp
          if (right.isInstanceOf[soot.jimple.InstanceInvokeExpr]) {
            val method = right.asInstanceOf[soot.jimple.InstanceInvokeExpr]
            updateAllocationSites(method.getMethod, visitedMethods += new VisitedMethods(method.getMethod, null, 1))
          }
          if (right.isInstanceOf[NewExpr] || right.isInstanceOf[NewArrayExpr] || right.isInstanceOf[StringConstant]) {
            allocationSites += (right -> createNode(m, unit, visitedMethods))
          }
        }
        else if (unit.isInstanceOf[soot.jimple.ReturnStmt]) {
          val exp = unit.asInstanceOf[soot.jimple.ReturnStmt].getOp
          if (exp.isInstanceOf[StringConstant]) {
            allocationSites += (exp -> createNode(m, unit, visitedMethods))
          }
        }

        if (unit.isInstanceOf[soot.jimple.InvokeStmt]) {
          val method = unit.asInstanceOf[soot.jimple.InvokeStmt]
          updateAllocationSites(method.getInvokeExpr.getMethod, visitedMethods += VisitedMethods(method.getInvokeExpr.getMethod, null, 1))
        }

      })
    }
  }

  class Transformer extends SceneTransformer {
    override def internalTransform(phaseName: String, options: util.Map[String, String]): Unit = {
      pointsToAnalysis = Scene.v().getPointsToAnalysis

      initAllocationSites()

      Scene.v().getEntryPoints.forEach(method => {
        traverse(method, new ListBuffer[VisitedMethods]())
        methods = methods + 1
      })
    }
  }

  def traverse(method: SootMethod, visitedMethods: ListBuffer[VisitedMethods], forceNewTraversal: Boolean = false): Unit = {
    if ((!forceNewTraversal) && shouldSkip(method)) {
      return
    }

    numberVisitedMethods += 1

    val startTime = System.nanoTime()

    //    visitedMethods += new VisitedMethods(method, null, method.getJavaSourceStartLineNumber)

    traversedMethods.add(method)

    val body = method.retrieveActiveBody()
    val graph = new ExceptionalUnitGraph(body)
    val defs = new SimpleLocalDefs(graph)

    traverseUnits(method, defs, visitedMethods)

    val endTime = System.nanoTime()
    val elapsedTime = (endTime - startTime) / 1000000

    val elapsedSeconds = elapsedTime / 1000.0 // time in seconds

    if (printDepthVisitedMethods) {
      val methodsString = visitedMethodsDepth.map(_.toString).mkString(", ")
      s"path: [$methodsString]"
      println(method.toString + "path:" + methodsString + "-> deep: " + visitedMethodsDepth.size + " time: " + elapsedSeconds)
    }

    traversedMethods.remove(method)
  }

  private def traverseUnits(method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val body = method.getActiveBody
    body.getUnits.forEach(unit => {
      val v = Statement.convert(unit)

      val auxVisitedMethod = new ListBuffer[VisitedMethods]()
      auxVisitedMethod.++=(visitedMethods)
      auxVisitedMethod += new VisitedMethods(method, unit, unit.getJavaSourceStartLineNumber)

      v match {
        case AssignStmt(base) => traverse(AssignStmt(base), method, defs, auxVisitedMethod)
        case InvokeStmt(base) => traverse(InvokeStmt(base), method, defs, auxVisitedMethod)
        case _ if analyze(unit) == SinkNode => traverseSinkStatement(v, method, defs, auxVisitedMethod)
        case _ =>
      }
    })
  }

  def traverse(assignStmt: AssignStmt, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val left = assignStmt.stmt.getLeftOp
    val right = assignStmt.stmt.getRightOp

    (left, right) match {
      case (p: Local, q: InstanceFieldRef) => loadRule(assignStmt.stmt, q, method, defs, visitedMethods)
      case (p: Local, q: StaticFieldRef) => loadStaticFieldRule(assignStmt.stmt, q, method, defs, visitedMethods)
      case (p: Local, q: ArrayRef) => loadArrayRule(assignStmt.stmt, q, method, defs, visitedMethods)
      case (p: Local, q: InvokeExpr) => invokeRule(assignStmt, q, method, defs, visitedMethods)
      case (p: Local, q: Local) => copyRule(assignStmt.stmt, q, method, defs, visitedMethods)
      case (p: Local, _) => copyRuleInvolvingExpressions(assignStmt.stmt, method, defs, visitedMethods)
      case (p: InstanceFieldRef, q: Object) => storeRule(assignStmt.stmt, q, p, method, defs, visitedMethods)
      case (p: StaticFieldRef, q: Object) => storeStaticFieldRule(assignStmt.stmt, q, p, method, defs, visitedMethods)
      case (p: JArrayRef, _) => storeArrayRule(assignStmt)
      case _ =>
    }

  }

  def traverse(stmt: InvokeStmt, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val exp = stmt.stmt.getInvokeExpr
    invokeRule(stmt, exp, method, defs, visitedMethods)
  }

  def traverseSinkStatement(statement: Statement, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    statement.base.getUseBoxes.forEach(box => {
      val value = box.getValue
      value match {
        case local: Local => copyRule(statement.base, local, method, defs, visitedMethods)
        case fieldRef: InstanceFieldRef => loadRule(statement.base, fieldRef, method, defs, visitedMethods)
        case fieldRef: StaticFieldRef => loadStaticFieldRule(statement.base, fieldRef, method, defs, visitedMethods)
        case _ =>
        // TODO:
        //   we have to think about other cases here.
      }
    })
  }

  private def statementUseField(stmtField: jimple.AssignStmt, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {

    //Add edge from defs statements fields to statement use
    stmtField.getLeftOp.getUseBoxes.forEach(stmt => {
      if (stmt.getValue.isInstanceOf[Local]) {
        val local = stmt.getValue.asInstanceOf[Local]

        defs.getDefsOfAt(local, stmtField).forEach(sourceStmt => {
          val sourceNode = createNode(method, sourceStmt, visitedMethods)
          val targetNode = createNode(method, stmtField, visitedMethods)
          updateGraph(sourceNode, targetNode)
        })
      }
    })
  }

  private def invokeRule(callStmt: Statement, exp: InvokeExpr, caller: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    if (analyze(callStmt.base) == SinkNode) {
      defsToCallOfSinkMethod(callStmt, exp, caller, defs, visitedMethods)
    }

    if (analyze(callStmt.base) == SourceNode || analyze(callStmt.base) == SinkNode) {
      val source = createNode(caller, callStmt.base, visitedMethods)
      svg.addNode(source)
    }

    //Add edge from defs statements to invoke statement use
    callStmt.base.getUseBoxes.forEach(stmt => {
      if (stmt.getValue.isInstanceOf[Local]) {
        val local = stmt.getValue.asInstanceOf[Local]

        defs.getDefsOfAt(local, callStmt.base).forEach(sourceStmt => {
          val sourceNode = createNode(caller, sourceStmt, visitedMethods)
          val targetNode = createNode(caller, callStmt.base, visitedMethods)
          updateGraph(sourceNode, targetNode)
        })
      }
    })

    val callGraph = Scene.v().getCallGraph
    val edges = callGraph.edgesOutOf(callStmt.base)

    if (edges.hasNext) {
      while (edges.hasNext) {
        val edge = edges.next()
        val callee = edge.getTgt().method()
        applyRulesAndTraverse(callStmt, exp, caller, callee, defs, visitedMethods)
      }
    } else {
      val callee = exp.getMethod
      applyRulesAndTraverse(callStmt, exp, caller, callee, defs, visitedMethods)
    }
  }

  private def applyRulesAndTraverse(callStmt: Statement, exp: InvokeExpr, caller: SootMethod, callee: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    for (r <- methodRules) {
      if (r.check(callee)) {
        r.apply(caller, callStmt.base.asInstanceOf[jimple.Stmt], defs, visitedMethods)
        return
      }
    }

    if (intraprocedural()) return

    if (!callee.hasActiveBody) return

    val body = callee.retrieveActiveBody()
    val g = new ExceptionalUnitGraph(body)
    val calleeDefs = new SimpleLocalDefs(g)

    var pmtCount = 0
    body.getUnits.forEach(s => {
      if (isThisInitStmt(exp, s)) {
        defsToThisObject(callStmt, caller, defs, s, exp, callee, visitedMethods)
      }
      else if (isParameterInitStmt(exp, pmtCount, s)) {
        defsToFormalArgs(callStmt, caller, defs, s, exp, callee, pmtCount, visitedMethods)
        pmtCount = pmtCount + 1
      }
      else if (isAssignReturnLocalStmt(callStmt.base, s)) {
        defsToCallSite(caller, callee, calleeDefs, callStmt.base, s, visitedMethods)
      }
      else if (isReturnStringStmt(callStmt.base, s)) {
        stringToCallSite(caller, callee, callStmt.base, s, visitedMethods)
      }
    })
    visitedMethodsDepth += callee.retrieveActiveBody().getMethod

    traverse(callee, visitedMethods)

    visitedMethodsDepth.remove(visitedMethodsDepth.size - 1)
  }

  private def applyPhantomMethodCallRule(callStmt: Statement, exp: InvokeExpr, caller: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
    val srcArg = exp.getArg(0)
    val destArg = exp.getArg(2)
    if (srcArg.isInstanceOf[Local] && destArg.isInstanceOf[Local]) {
      defs.getDefsOfAt(srcArg.asInstanceOf[Local], callStmt.base).forEach(srcArgDefStmt => {
        val sourceNode = createNode(caller, srcArgDefStmt, visitedMethods)
        val allocationNodes = findAllocationSites(destArg.asInstanceOf[Local])
        allocationNodes.foreach(targetNode => {
          updateGraph(sourceNode, targetNode)
        })
      })
    }
  }

  /*
     * This rule deals with the following situation:
     *
     * (*) p = q
     *
     * In this case, we create an edge from defs(q)
     * to the statement p = q.
     */
  protected def copyRule(targetStmt: soot.Unit, local: Local, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
    defs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
      val source = createNode(method, sourceStmt, visitedMethods)
      val target = createNode(method, targetStmt, visitedMethods)
      updateGraph(source, target)
    })
  }

  /*
   * This rule deals with the following situation:
   *
   * (*) p = q + r
   *
   * In this case, we create and edge from defs(q) and
   * from defs(r) to the statement p = q + r
   */
  def copyRuleInvolvingExpressions(stmt: jimple.AssignStmt, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
    stmt.getRightOp.getUseBoxes.forEach(box => {
      if (box.getValue.isInstanceOf[Local]) {
        val local = box.getValue.asInstanceOf[Local]
        copyRule(stmt, local, method, defs, visitedMethods)
      }
    })
  }

  /*
   * This rule deals with the following situations:
   *
   *  (*) p = q.f
   */
  protected def loadRule(stmt: soot.Unit, ref: InstanceFieldRef, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val base = ref.getBase
    // value field of a string.
    val className = ref.getFieldRef.declaringClass().getName
    if ((className == "java.lang.String") && ref.getFieldRef.name == "value") {
      if (base.isInstanceOf[Local]) {
        defs.getDefsOfAt(base.asInstanceOf[Local], stmt).forEach(source => {
          val sourceNode = createNode(method, source, visitedMethods)
          val targetNode = createNode(method, stmt, visitedMethods)
          updateGraph(sourceNode, targetNode)
        })
      }
      return;
    }
    // default case
    if (base.isInstanceOf[Local]) {
      var allocationNodes = findAllocationSites(base.asInstanceOf[Local], false, ref.getField)

      if (allocationNodes.isEmpty) {
        allocationNodes = findAllocationSites(base.asInstanceOf[Local], true, ref.getField)
      }

      if (allocationNodes.isEmpty) {
        allocationNodes = findFieldStores(base.asInstanceOf[Local], ref.getField, visitedMethods)
      }

      allocationNodes.foreach(source => {
        val target = createNode(method, stmt, visitedMethods)
        updateGraph(source, target)
        svg.getAdjacentNodes(source).getOrElse(List()).foreach(s => updateGraph(s, target))
      })

      // create an edge from the base defs to target
      // if an object is tainted, we should propagate the taint to all
      // fields as well. Not completely sure if this should be
      // the case.
      if (propagateObjectTaint()) {
        defs.getDefsOfAt(base.asInstanceOf[Local], stmt).forEach(source => {
          val sourceNode = createNode(method, source, visitedMethods)
          val targetNode = createNode(method, stmt, visitedMethods)
          updateGraph(sourceNode, targetNode)
        })
      }
    }
  }

  protected def loadArrayRule(targetStmt: soot.Unit, ref: ArrayRef, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val base = ref.getBase

    if (base.isInstanceOf[Local]) {
      val local = base.asInstanceOf[Local]

      defs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
        val source = createNode(method, sourceStmt, visitedMethods)
        val target = createNode(method, targetStmt, visitedMethods)
        updateGraph(source, target)
      })

      val stores = arrayStores.getOrElseUpdate(local, List())
      stores.foreach(sourceStmt => {
        val source = createNode(method, sourceStmt, visitedMethods)
        val target = createNode(method, targetStmt, visitedMethods)
        updateGraph(source, target)
      })
    }
  }

  protected def loadStaticFieldRule(stmt: soot.Unit, ref: StaticFieldRef, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val allocationNodes = findAllocationSitesForStaticField(ref.getField)
    val target = createNode(method, stmt, visitedMethods)
    allocationNodes.foreach(source => {
      updateGraph(source, target)
    })
  }

  protected def storeStaticFieldRule(stmt: jimple.AssignStmt, rightOp: Object, ref: StaticFieldRef, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    if (rightOp.isInstanceOf[Local]) {
      val sourceLocal = rightOp.asInstanceOf[Local]
      defs.getDefsOfAt(sourceLocal, stmt).forEach(sourceStmt => {
        val source = createNode(method, sourceStmt, visitedMethods)
        val allocationNodes = findAllocationSitesForStaticField(ref.getField)
        allocationNodes.foreach(target => {
          updateGraph(source, target)
        })
      })
    }
  }

  /*
   * This rule deals with statements in the form:
   *
   * (*) p.f = expression
   */
  private def storeRule(targetStmt: jimple.AssignStmt, q: Object, fieldRef: InstanceFieldRef, method: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
    if (q.isInstanceOf[Local]) {
      val local = targetStmt.getRightOp.asInstanceOf[Local]
      if (fieldRef.getBase.isInstanceOf[Local]) {
        val base = fieldRef.getBase.asInstanceOf[Local]
        if (fieldRef.getField.getDeclaringClass.getName == "java.lang.String" && fieldRef.getField.getName == "value") {
          defs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
            val source = createNode(method, sourceStmt, visitedMethods)
            val allocationNodes = findAllocationSites(base)
            allocationNodes.foreach(targetNode => {
              updateGraph(source, targetNode)
            })
          })
        }
        else {

          //        val allocationNodes = findAllocationSites(base)

          //        val allocationNodes = findAllocationSites(base, true, fieldRef.getField)
          //        if(!allocationNodes.isEmpty) {
          //          allocationNodes.foreach(targetNode => {
          defs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
            val source = createNode(method, sourceStmt, visitedMethods)
            val target = createNode(method, targetStmt, visitedMethods)
            updateGraph(source, target)
          })
          //          })
          //        }

        }
      }

    }

    statementUseField(targetStmt, method, defs, visitedMethods)

  }

  def storeArrayRule(assignStmt: AssignStmt) {
    val l = assignStmt.stmt.getLeftOp.asInstanceOf[JArrayRef].getBase.asInstanceOf[Local]
    val stores = assignStmt.stmt :: arrayStores.getOrElseUpdate(l, List())
    arrayStores.put(l, stores)
  }

  private def defsToCallSite(caller: SootMethod, callee: SootMethod, calleeDefs: SimpleLocalDefs, callStmt: soot.Unit, retStmt: soot.Unit, visitedMethods: ListBuffer[VisitedMethods]) = {
    val target = createNode(caller, callStmt, visitedMethods)

    val local = retStmt.asInstanceOf[ReturnStmt].getOp.asInstanceOf[Local]
    calleeDefs.getDefsOfAt(local, retStmt).forEach(sourceStmt => {
      val source = createNode(callee, sourceStmt, visitedMethods)
      val csCloseLabel = createCSCloseLabel(caller, callStmt, callee)
      svg.addEdge(source, target, csCloseLabel)

      if (local.getType.isInstanceOf[ArrayType]) {
        val stores = arrayStores.getOrElseUpdate(local, List())
        stores.foreach(sourceStmt => {
          val source = createNode(callee, sourceStmt, visitedMethods)
          val csCloseLabel = createCSCloseLabel(caller, callStmt, callee)
          svg.addEdge(source, target, csCloseLabel)
        })
      }
    })
  }

  private def stringToCallSite(caller: SootMethod, callee: SootMethod, callStmt: soot.Unit, retStmt: soot.Unit, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val target = createNode(caller, callStmt, visitedMethods)
    val source = createNode(callee, retStmt, visitedMethods)
    svg.addEdge(source, target)
  }

  private def defsToThisObject(callStatement: Statement, caller: SootMethod, calleeDefs: SimpleLocalDefs, targetStmt: soot.Unit, expr: InvokeExpr, callee: SootMethod, visitedMethods: ListBuffer[VisitedMethods]): Unit = {
    val invokeExpr = expr match {
      case e: VirtualInvokeExpr => e
      case e: SpecialInvokeExpr => e
      case e: InterfaceInvokeExpr => e
      case _ => null //TODO: not sure if the other cases
      // are also relevant here. Otherwise,
      // we can just match with InstanceInvokeExpr
    }

    if (invokeExpr != null) {
      if (invokeExpr.getBase.isInstanceOf[Local]) {

        val target = createNode(callee, targetStmt, visitedMethods)

        val base = invokeExpr.getBase.asInstanceOf[Local]
        calleeDefs.getDefsOfAt(base, callStatement.base).forEach(sourceStmt => {
          val source = createNode(caller, sourceStmt, visitedMethods)
          val csOpenLabel = createCSOpenLabel(caller, callStatement.base, callee)
          svg.addEdge(source, target, csOpenLabel)
        })
      }
    }
  }

  private def defsToFormalArgs(stmt: Statement, caller: SootMethod, defs: SimpleLocalDefs, assignStmt: soot.Unit, exp: InvokeExpr, callee: SootMethod, pmtCount: Int, visitedMethods: ListBuffer[VisitedMethods]) = {
    val target = createNode(callee, assignStmt, visitedMethods)

    val local = exp.getArg(pmtCount).asInstanceOf[Local]
    defs.getDefsOfAt(local, stmt.base).forEach(sourceStmt => {
      val source = createNode(caller, sourceStmt, visitedMethods)
      val csOpenLabel = createCSOpenLabel(caller, stmt.base, callee)
      svg.addEdge(source, target, csOpenLabel)
    })
  }

  private def defsToCallOfSinkMethod(stmt: Statement, exp: InvokeExpr, caller: SootMethod, defs: SimpleLocalDefs, visitedMethods: ListBuffer[VisitedMethods]) = {
    // edges from definitions to args
    exp.getArgs.stream().filter(a => a.isInstanceOf[Local]).forEach(a => {
      val local = a.asInstanceOf[Local]
      val targetStmt = stmt.base
      defs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
        val source = createNode(caller, sourceStmt, visitedMethods)
        val target = createNode(caller, targetStmt, visitedMethods)
        updateGraph(source, target)
      })

      if (local.getType.isInstanceOf[ArrayType]) {
        val stores = arrayStores.getOrElseUpdate(local, List())
        stores.foreach(sourceStmt => {
          val source = createNode(caller, sourceStmt, visitedMethods)
          val target = createNode(caller, targetStmt, visitedMethods)
          updateGraph(source, target)
        })
      }
    })
    // edges from definition to base object of an invoke expression
    if (isFieldSensitiveAnalysis() && exp.isInstanceOf[InstanceInvokeExpr]) {
      if (exp.asInstanceOf[InstanceInvokeExpr].getBase.isInstanceOf[Local]) {
        val local = exp.asInstanceOf[InstanceInvokeExpr].getBase.asInstanceOf[Local]
        val targetStmt = stmt.base
        defs.getDefsOfAt(local, targetStmt).forEach(sourceStmt => {
          val source = createNode(caller, sourceStmt, visitedMethods)
          val target = createNode(caller, targetStmt, visitedMethods)
          updateGraph(source, target)
        })
      }
    }
  }

  /*
   * creates a graph node from a sootMethod / sootUnit
   */
  def createNode(method: SootMethod, stmt: soot.Unit, visitedMethods: ListBuffer[VisitedMethods]): StatementNode =
    svg.createNode(method, stmt, analyze, visitedMethods)


  def createCSOpenLabel(method: SootMethod, stmt: soot.Unit, callee: SootMethod): CallSiteLabel = {
    val statement = br.unb.cic.soot.graph.Statement(method.getDeclaringClass.toString, method.getSignature, stmt.toString,
      stmt.getJavaSourceStartLineNumber, stmt, method)
    CallSiteLabel(ContextSensitiveRegion(statement, callee.toString), CallSiteOpenLabel)
  }

  def createCSCloseLabel(method: SootMethod, stmt: soot.Unit, callee: SootMethod): CallSiteLabel = {
    val statement = br.unb.cic.soot.graph.Statement(method.getDeclaringClass.toString, method.getSignature, stmt.toString,
      stmt.getJavaSourceStartLineNumber, stmt, method)
    CallSiteLabel(ContextSensitiveRegion(statement, callee.toString), CallSiteCloseLabel)
  }

  def isThisInitStmt(expr: InvokeExpr, unit: soot.Unit): Boolean =
    unit.isInstanceOf[IdentityStmt] && unit.asInstanceOf[IdentityStmt].getRightOp.isInstanceOf[ThisRef]

  def isParameterInitStmt(expr: InvokeExpr, pmtCount: Int, unit: soot.Unit): Boolean =
    unit.isInstanceOf[IdentityStmt] && unit.asInstanceOf[IdentityStmt].getRightOp.isInstanceOf[ParameterRef] && expr.getArg(pmtCount).isInstanceOf[Local]

  def isAssignReturnLocalStmt(callSite: soot.Unit, unit: soot.Unit): Boolean =
    unit.isInstanceOf[ReturnStmt] && unit.asInstanceOf[ReturnStmt].getOp.isInstanceOf[Local] &&
      callSite.isInstanceOf[soot.jimple.AssignStmt]

  def isReturnStringStmt(callSite: soot.Unit, unit: soot.Unit): Boolean =
    unit.isInstanceOf[ReturnStmt] && unit.asInstanceOf[ReturnStmt].getOp.isInstanceOf[StringConstant] &&
      callSite.isInstanceOf[soot.jimple.AssignStmt]

  def findAllocationSites(local: Local, oldSet: Boolean = true, field: SootField = null): ListBuffer[GraphNode] = {
    if (pointsToAnalysis != null) {
      val reachingObjects = if (field == null) pointsToAnalysis.reachingObjects(local)
      else pointsToAnalysis.reachingObjects(local, field)

      if (reachingObjects != null && !reachingObjects.isEmpty) {
        val res = findAllocationSitesFromPS(reachingObjects, oldSet)
        if (res.nonEmpty) return res
      }
    }
    findAllocationSitesByType(local, field)
  }

  def findAllocationSitesForStaticField(field: SootField): ListBuffer[GraphNode] = {
    if (pointsToAnalysis != null) {
      val reachingObjects = pointsToAnalysis.reachingObjects(field)
      if (reachingObjects != null && !reachingObjects.isEmpty) {
        val res = findAllocationSitesFromPS(reachingObjects, true)
        if (res.nonEmpty) return res
      }
    }
    // For static fields, fallback to type compatibility if possible
    val res = new ListBuffer[GraphNode]()
    val fieldType = field.getType
    val hierarchy = Scene.v().getOrMakeFastHierarchy

    for ((key, node) <- allocationSites) {
      val keyType = key match {
        case n: NewExpr => n.getType
        case n: NewArrayExpr => n.getType
        case n: StringConstant => n.getType
        case _ => null
      }
      if (node != null && keyType != null && (keyType == fieldType || (keyType.isInstanceOf[RefType] && fieldType.isInstanceOf[RefType] && hierarchy.canStoreType(keyType, fieldType)))) {
        res += node
      }
    }
    res
  }

  private def findAllocationSitesFromPS(reachingObjects: PointsToSet, oldSet: Boolean): ListBuffer[GraphNode] = {
    val v = new AllocationVisitor()
    if (reachingObjects.isInstanceOf[DoublePointsToSet]) {
      val allocations = if (oldSet) reachingObjects.asInstanceOf[DoublePointsToSet].getOldSet
      else reachingObjects.asInstanceOf[DoublePointsToSet].getNewSet
      if (allocations.isInstanceOf[PointsToSetInternal]) {
        allocations.asInstanceOf[PointsToSetInternal].forall(v)
      }
    } else if (reachingObjects.isInstanceOf[PointsToSetInternal]) {
      reachingObjects.asInstanceOf[PointsToSetInternal].forall(v)
    }
    v.allocationNodes
  }

  /**
   * Fallback para encontrar allocation sites quando não há PAG disponível (CHA/RTA).
   * Usa compatibilidade de tipo via FastHierarchy (mesma estratégia da OverrideAssignment).
   *
   * Para cada nó no grafo que seja um AssignStmt com NewExpr no right-op,
   * verifica se o tipo alocado é compatível (mesmo tipo ou subtipo) com o tipo da variável local.
   * Se um field for especificado, também verifica se há um store para esse field no nó.
   */
  def findAllocationSitesByType(local: Local, field: SootField = null): ListBuffer[GraphNode] = {
    val res = new ListBuffer[GraphNode]()
    val localType = local.getType

    val targetType = if (field != null) field.getType else local.getType

    val hierarchy = Scene.v().getOrMakeFastHierarchy

    for ((key, node) <- allocationSites) {
      val allocType = key match {
        case newExpr: NewExpr => newExpr.getBaseType
        case newArrayExpr: NewArrayExpr => newArrayExpr.getType
        case _: StringConstant => RefType.v("java.lang.String")
        case _ => null
      }

      if (allocType != null && isTypeCompatible(targetType, allocType, hierarchy)) {
        if (field == null || hasAnyFieldStore(field)) {
          if (node != null) res += node
        }
      }
    }
    res
  }

  private def hasAnyFieldStore(field: SootField): Boolean = {
    storedFields.contains(field)
  }

  /**
   * Verifica compatibilidade de tipo usando FastHierarchy.canStoreType,
   * seguindo o padrão da OverrideAssignment.isSameOrSubtype.
   *
   * Retorna true se:
   * - Os tipos são iguais, OU
   * - Um é subtipo do outro (em qualquer direção)
   */
  private def isTypeCompatible(typeA: soot.Type, typeB: soot.Type, hierarchy: FastHierarchy): Boolean = {
    if (typeA == typeB || typeA.equals(typeB)) return true

    (typeA, typeB) match {
      case (a: RefType, b: RefType) =>
        hierarchy.canStoreType(a, b) || hierarchy.canStoreType(b, a)
      case (a: ArrayType, b: ArrayType) =>
        (a.baseType, b.baseType) match {
          case (ba: RefType, bb: RefType) =>
            hierarchy.canStoreType(ba, bb) || hierarchy.canStoreType(bb, ba)
          case _ => a.baseType.equals(b.baseType)
        }
      case _ => false
    }
  }

  /**
   * Verifica se existe um store para o field especificado em algum nó do grafo
   * cujo allocation site corresponde ao nó dado.
   */

  /*
   * a class to visit the allocation nodes of the objects that
   * a field might point to.
   *
   * @param method method of the statement stmt
   * @param stmt statement with a load operation
   */
  class AllocationVisitor() extends P2SetVisitor {

    var allocationNodes = new ListBuffer[GraphNode]()

    override def visit(n: pag.Node): Unit = {
      if (n.isInstanceOf[AllocNode]) {
        val allocationNode = n.asInstanceOf[AllocNode]

        var stmt: StatementNode = null

        if (allocationNode.getNewExpr.isInstanceOf[NewExpr]) {
          if (allocationSites.contains(allocationNode.getNewExpr.asInstanceOf[NewExpr])) {
            stmt = allocationSites(allocationNode.getNewExpr.asInstanceOf[NewExpr])
          }
        }
        else if (allocationNode.getNewExpr.isInstanceOf[NewArrayExpr]) {
          if (allocationSites.contains(allocationNode.getNewExpr.asInstanceOf[NewArrayExpr])) {
            stmt = allocationSites(allocationNode.getNewExpr.asInstanceOf[NewArrayExpr])
          }
        }
        else if (allocationNode.getNewExpr.isInstanceOf[String]) {
          val str: StringConstant = StringConstant.v(allocationNode.getNewExpr.asInstanceOf[String])
          stmt = allocationSites.getOrElseUpdate(str, null)
        }

        if (stmt != null) {
          allocationNodes += stmt
        }
      }
    }
  }

  /**
   * Override this method in the case that
   * a complete graph should be generated.
   *
   * Otherwise, only nodes that can be reached from
   * source nodes will be in the graph
   *
   * @return true for a full sparse version of the graph.
   *         false otherwise.
   * @deprecated
   */
  def runInFullSparsenessMode() = true

  //  def findFieldStores(local: Local, field: SootField, visitedMethods: ListBuffer[VisitedMethods]): ListBuffer[GraphNode] = {
  //    val res: ListBuffer[GraphNode] = new ListBuffer[GraphNode]()
  //    for (node <- svg.nodes()) {
  //      if (node.unit().isInstanceOf[soot.jimple.AssignStmt]) {
  //        val assignment = node.unit().asInstanceOf[soot.jimple.AssignStmt]
  //        if (assignment.getLeftOp.isInstanceOf[InstanceFieldRef]) {
  //          val base = assignment.getLeftOp.asInstanceOf[InstanceFieldRef].getBase.asInstanceOf[Local]
  //          if (pointsToAnalysis.reachingObjects(base).hasNonEmptyIntersection(pointsToAnalysis.reachingObjects(local))) {
  //            if (field.equals(assignment.getLeftOp.asInstanceOf[InstanceFieldRef].getField)) {
  //              res += createNode(node.method(), node.unit(), visitedMethods)
  //            }
  //          }
  //        }
  //      }
  //    }
  //    return res
  //  }

  def findFieldStores(local: Local, field: SootField, visitedMethods: ListBuffer[VisitedMethods]): ListBuffer[GraphNode] = {
    val res: ListBuffer[GraphNode] = new ListBuffer[GraphNode]()
    try {
      for (node <- svg.nodes()) {
        if (node.unit().isInstanceOf[soot.jimple.AssignStmt]) {
          val assignment = node.unit().asInstanceOf[soot.jimple.AssignStmt]
          if (assignment.getLeftOp.isInstanceOf[InstanceFieldRef]) {
            val instanceRef = assignment.getLeftOp.asInstanceOf[InstanceFieldRef]
            val base = instanceRef.getBase match {
              case l: Local => l
              case _ => null
            }
            if (base != null && local != null && field.equals(instanceRef.getField)) {
              if (pointsToAnalysis != null) {
                val baseObjs = pointsToAnalysis.reachingObjects(base)
                val localObjs = pointsToAnalysis.reachingObjects(local)

                if (baseObjs != null && localObjs != null
                  && !baseObjs.isEmpty && !localObjs.isEmpty) {
                  // SPARK/VTA: usa interseção de points-to (preciso)
                  if (baseObjs.hasNonEmptyIntersection(localObjs)) {
                    res += createNode(node.method(), node.unit(), visitedMethods)
                  }
                }
              } else {
                // CHA/RTA: points-to vazio, fallback por tipo
                val hierarchy = Scene.v().getOrMakeFastHierarchy
                if (isTypeCompatible(base.getType, local.getType, hierarchy)) {
                  res += createNode(node.method(), node.unit(), visitedMethods)
                }
              }
            }
          }
        }
      }
    } catch {
      case _: Exception =>
    }
    res
  }

  //  /*
  //   * It either updates the graph or not, depending on
  //   * the types of the nodes.
  //   */

  def containsNodeDF(node: StatementNode): StatementNode = {
    for (n <- svg.edges()) {
      var auxNodeFrom = n.from.asInstanceOf[StatementNode]
      var auxNodeTo = n.to.asInstanceOf[StatementNode]
      if (auxNodeFrom != null && auxNodeFrom.equals(node)) return n.from.asInstanceOf[StatementNode]
      if (auxNodeTo != null && auxNodeTo.equals(node)) return n.to.asInstanceOf[StatementNode]
    }
    return null
  }

  def updateGraph(source: GraphNode, target: GraphNode, forceNewEdge: Boolean = false): Boolean = {
    var res = false
    if (source == null || target == null) return false

    if (!runInFullSparsenessMode() || true) {
      addNodeAndEdgeDF(source.asInstanceOf[StatementNode], target.asInstanceOf[StatementNode])

      res = true
    }
    return res
  }

  def addNodeAndEdgeDF(from: StatementNode, to: StatementNode): Unit = {
    var auxNodeFrom = containsNodeDF(from)
    var auxNodeTo = containsNodeDF(to)
    if (auxNodeFrom != null) {
      if (auxNodeTo != null) {
        svg.addEdge(auxNodeFrom, auxNodeTo)
      } else {
        svg.addEdge(auxNodeFrom, to)
      }
    } else {
      if (auxNodeTo != null) {
        svg.addEdge(from, auxNodeTo)
      } else {
        svg.addEdge(from, to)
      }
    }
  }

  def setPrintDepthVisitedMethods(printDepthVisitedMethods: Boolean) {
    this.printDepthVisitedMethods = printDepthVisitedMethods
  }

  def getNumberVisitedMethods(): Int = {
    return numberVisitedMethods
  }

  def getCountNoEdges: Int = countNoEdges

  def getCountWithEdges: Int = countWithEdges

  private def shouldSkip(method: SootMethod): Boolean = {

    val isCycle = traversedMethods.contains(method)
    val relativeTraversed = hasRelativeBeenTraversed(method)

    val res = method.isPhantom ||
      isCycle ||
      relativeTraversed ||
      (isLimited() && visitedMethodsDepth.size >= maxDepth()) ||
      isMethodDefinedInObject(method)

    res
  }

  private def hasRelativeBeenTraversed(method: SootMethod): Boolean = {
    visitedMethodsDepth.exists(m => haveCommonAncestorClass(method, m))
  }

  private def haveCommonAncestorClass(method1: SootMethod, method2: SootMethod): Boolean = {
    val ancestors1 = getAncestors(method1).asScala
    val ancestors2 = getAncestors(method2).asScala

    for (ancestor1 <- ancestors1) {
      for (ancestor2 <- ancestors2) {
        try {
          val ancestorMethod1 = ancestor1.getMethod(method1.getName, method1.getParameterTypes)
          val ancestorMethod2 = ancestor2.getMethod(method2.getName, method2.getParameterTypes)
          return ancestorMethod1 == ancestorMethod2
        } catch {
          case _: Exception => // ignore
        }
      }
    }
    false
  }

  private def getAncestors(method: SootMethod): java.util.Set[soot.SootClass] = {
    val ancestors = new java.util.HashSet[soot.SootClass]()
    var sootClass = method.getDeclaringClass
    ancestors.add(sootClass)
    while (sootClass.hasSuperclass) {
      sootClass = sootClass.getSuperclass
      ancestors.add(sootClass)
    }

    // Get interfaces recursively
    val interfaces = new java.util.HashSet[soot.SootClass]()
    val queue = new java.util.LinkedList[soot.SootClass]()
    ancestors.asScala.foreach(c => queue.add(c))

    while (!queue.isEmpty) {
      val c = queue.poll()
      c.getInterfaces.asScala.foreach(i => {
        if (!ancestors.contains(i)) {
          ancestors.add(i)
          queue.add(i)
        }
      })
    }

    val ancestorsWithMethod = new java.util.HashSet[soot.SootClass]()
    ancestors.asScala.foreach(ancestor => {
      try {
        val ancestorMethod = ancestor.getMethod(method.getName, method.getParameterTypes)
        if (ancestorMethod != null) {
          ancestorsWithMethod.add(ancestor)
        }
      } catch {
        case _: Exception => // ignore
      }
    })
    ancestorsWithMethod
  }

  private def isMethodDefinedInObject(method: SootMethod): Boolean = {
    val methodName = method.getName
    methodName.equals("toString") ||
      methodName.equals("hashCode") ||
      methodName.equals("equals") ||
      methodName.equals("getClass") ||
      methodName.equals("notify") ||
      methodName.equals("notifyAll") ||
      methodName.equals("wait")
  }

}
