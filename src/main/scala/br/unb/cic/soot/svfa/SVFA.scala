package br.unb.cic.soot.svfa


import com.google.common.base.Stopwatch
import soot._

import java.util.Collections
import java.util.concurrent.TimeUnit

/**
 * Base class for all implementations
 * of SVFA algorithms.
 */
abstract class SVFA extends SootConfiguration {

  var svg = new br.unb.cic.soot.graph.Graph()

  var packageExecutionTimes = new java.util.HashMap[String, java.lang.Long]()

  def buildSparseValueFlowGraph() {
    configureSoot()
    beforeGraphConstruction()
    val (pack, t) = createSceneTransform()
    PackManager.v().getPack(pack).add(t)
    configurePackages().foreach(p => {
      val stopwatch = Stopwatch.createStarted
      PackManager.v().getPack(p).apply()
      val elapsedMs = stopwatch.elapsed(TimeUnit.MILLISECONDS)
      packageExecutionTimes.put(p, elapsedMs)
    })
    afterGraphConstruction()
  }

  def getPackageExecutionTimes: java.util.Map[String, java.lang.Long] =
    Collections.unmodifiableMap(packageExecutionTimes)

  def svgToDotModel(): String = {
    svg.toDotModel()
  }

  def reportConflictsSVG() = {
    svg.reportConflicts()
  }

  def reportConflictsSVGJSON() = {
      svg.reportConflictsJSON()
  }

}
