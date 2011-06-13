// rudolf muehlbauer
// 0655329

// petri net / place transition network:
// * calculate reachability graph
// * find deadlocks

// definitions & names from:
// [1] Bernd Baumgarten, Petri-Netze: Grundlagen und Anwendungen



/**
 * common ancestor for Place and Transition to make the Network definition
 * [1,p. 50] OO-Compatible
 */
abstract class Node(val name: String)


/**
 * Model for a Place
 *
 * k: Capacity of the Place
 */
case class Place(override val name: String, val k: Int) extends Node(name)

/**
 * Model for a Transition
 */
case class Transition(override val name: String) extends Node(name) {
  override def toString : String = name
}




/**
 * Edge models an Edge in a PTN. An edge can either be Place->Transition or vice versa.
 *
 * I could not manage to make scala check this constraint for me, so i added a runtime-check
 *
 * w: weight of the Edge
 */
case class Edge(val from: Node, val to: Node, val w: Int = 1) {

  // add a runtime type check: Edge is P->T or T->P
  (from,to) match {
    case (a:Place, b:Transition) => {}
    case (a:Transition, b:Place) => {}
    case other => throw new IllegalArgumentException("Edge is neither P->T or T->P")
  }
}

class PlaceTransEdge(val from: Place, val to: Transition, val w: Int = 1) extends Edge
class TransPlaceEdge(val from: Transition, val to: Place, val w: Int = 1) extends Edge



/**
 * class PetriNet implements the model for a Place/Transition network
 */
case class PetriNet(val P : Set[Place],
                    val T : Set[Transition],
                    val F : Set[Edge]) {

  def printDot():Unit = {
    println("digraph {")
    println(" node[shape=circle,fixedsize=true]; " + P.map(p => p.name + "[label=\""+p.name+"\\n"+p.k+"\"]").mkString(";"))
    println(" node[shape=box]; " + T.map(_.name).mkString(";"))
    F foreach ((f:Edge) => println(f.from.name + "->" + f.to.name + "[label=\"" + f.w + "\"]"))
    println(" overlap=false")
    println(" label=\"Scala PetriNet example\"")
    println("}")
  }

  // [1, p. 51]
  def inputPlaces(t:Transition)  = P.filter( p=> F.exists( f=> f.to == t && f.from == p))
  def outputPlaces(t:Transition) = P.filter( p=> F.exists( f=> f.to == p && f.from == t))
  def inputTransitions(p:Place)  = T.filter( t=> F.exists( f=> f.to == p && f.from == t))
  def outputTransitions(p:Place) = T.filter( t=> F.exists( f=> f.to == t && f.from == p))


  def W(from:Node, to:Node) = F.find( f=> f.from == from && f.to == to ).get.w
  def K(p:Place) = p.k

  override def hashCode = P.hashCode ^ T.hashCode ^ F.hashCode
  override def equals(that:Any) = that match {
    case that: PetriNet => that.P == P && that.T == T && that.F == F
    case other => false
  }
}


/**
 * general graph traversal trait for calculated successor nodes
 */
trait HasSuccessor[M,T] {

  def successors: Set[(M,T,M)] = activatedTransitions.map( t => (this.asInstanceOf[M],t,applyTransition(t)) )

  /* abstract */ def activatedTransitions : Set[T]
  /* abstract */ def applyTransition(a: T) : M
}

/**
 * Marking assigns the number of marks to every place in the PTN
 */
case class Marking(val pn:PetriNet, val M: Map[Place,Int]) extends HasSuccessor[Marking,Transition] {

  // aggregating forward
  val W = pn.W _
  val K = pn.K _

  val isComplete = pn.P.forall( M.contains(_) )
  val isSound = M.keys.forall (pn.P.contains(_))
  val isWithinCapacity = M.keys.forall( (p) => (M(p) <= K(p)))

  val isValid = isComplete && isSound && isWithinCapacity


  if (!isValid) throw new IllegalArgumentException("Marking is not valid")

  // [1, p. 81]
  def isActivated(t:Transition) =
    pn.inputPlaces(t).forall ( p => M(p) >= W(p,t) ) && pn.outputPlaces(t).forall( p => M(p) <= K(p) - W(t,p) )

  val activatedTransitions = pn.T.filter(isActivated(_))

  def applyTransition(t:Transition) = {
    if (!isActivated(t)) throw new IllegalArgumentException("Transition " + t + " is not activated")
    Marking(pn, M.map( me => {

      val (p,mi) = me

      val in = pn.inputPlaces(t)
      val out = pn.outputPlaces(t)

      // [1, p. 81]
      if ((in &~ out) contains p)      p -> (mi - W(p,t))
      else if ((out &~ in) contains p) p -> (mi + W(t,p))
      else if ((out & in) contains p)  p -> (mi - W(p,t) + W(t,p))
      else p -> mi
    }))
  }

  override def toString : String =
    "["+ M.keys.map( p => p.name + "=" + M(p) ).mkString(",") + "]"

  override def equals(that:Any) = that match {
    case that: Marking => that.pn == pn && that.M == M
    case other => false
  }

  override def hashCode = pn.hashCode ^ M.hashCode
}


/**
 * analyze implements the needed analysis functions
 */
object analyze {

  // search strategies

  def bfs[T](s: Set[T]): T = s head
  def dfs[T](s: Set[T]): T = s last

  def traverse[M <: HasSuccessor[M,T] ,T](m0: M, tfn: (Set[M] => M) = bfs _ ) = {
    var reached : Set[M] = Set(m0)
    var run : Set[(M,T,M)] = Set()
    var done : Set[M] = Set()
    var i = 1
    val doLog = false

    // just to have an awesome andThen somewhere:
    val not_run = ( run.contains(_) ) andThen ( !_ )

    while (reached.size > done.size) {

      val m = (reached &~ done) last

      if (doLog)
        println("--------------------------------\n" +
                "m:" + m +
                "\nreached:" + reached.mkString("\n") +
                "\ndone:"+done.mkString("\n") +
                "\nrun:" +run.mkString("\n"))


      val suc_new = m.successors.filter(not_run(_))
      if (!suc_new.isEmpty) {
        suc_new.foreach( s => {
          reached += s._3
          run += s
        })
      } else {
        done += m
      }
    }
    (done,run)
  }


  //  def findDeadlock[M<: HasSuccessor[M,T],T](reachGraph:Set[(M,T,M)]) =
  //    reachGraph.filter(_.successors.isEmpty).foreach( d =>
  //      println("marking has a deadlock: " + d) )

  // [1, p. 137]
  def schwach_lebendig[M<: HasSuccessor[M,T],T](pn:PetriNet, reachSet:Set[M], reachGraph:Set[(M,T,M)]) =
    reachSet.forall( m => reachGraph.exists( m == _._1) )

  def t_aktivierbar[M<: HasSuccessor[M,T],T](t:T, reachGraph:Set[(M,T,M)]) =
    reachGraph.exists( t == _._2 )

  //
  def stark_lebendig[M<:HasSuccessor[M,T],T](pn:PetriNet, reachSet:Set[M], reachGraph:Set[(M,T,M)]) =
    reachSet.forall( m1 => {
      pn.T.forall ( t => {
        val (m2_set, m2_graph) = traverse[M,T](m1, dfs)
        m2_graph.exists(t == _._2 )
      })
    })


  // [1, p. 157]
  def konservativ[M<:HasSuccessor[M,T],T](pn:PetriNet, reachSet:Set[M], reachGraph:Set[(M,T,M)]) =
    reachSet.forall ( _ match {
      case m: Marking => m.M.values.sum > 0
      case other => false
    } )


  def analyze_all(pn:PetriNet, m: Marking, n:String) = {

    val (reachSet,reachGraph) = traverse[Marking,Transition](m, dfs)

    println()
    println("result for "+n+":")
    println(reachGraph mkString("\n"))

    println("schwach lebendig: " + schwach_lebendig[Marking,Transition](pn, reachSet, reachGraph))
    println("stark lebendig: " + stark_lebendig[Marking,Transition](pn, reachSet, reachGraph))
    println("konservativ: "  + konservativ[Marking,Transition](pn, reachSet, reachGraph))
  }
}




object YBeispiel extends App {

  import analyze._;


  // Beispiel 1
  {
    // sample ptn, [1, p. 80]

    val p1 = Place("p1", 1000)
    val p2 = Place("p2", 1000)
    val p3 = Place("p3", 1)
    val p4 = Place("p4", 1000)

    val t1 = Transition("t1")
    val t2 = Transition("t2")
    val t3 = Transition("t3")

    val pn = PetriNet(Set(p1, p2, p3, p4),
                      Set(t1, t2, t3),
                      Set(Edge(t1,p1),
                          Edge(t1,p2),
                          Edge(p1,t2),
                          Edge(p2,t3),
                          Edge(t2,p3),
                          Edge(t2,p4),
                          Edge(t3,p4),
                          Edge(p4,t1,w=2)))

    val m = Marking(pn,
                    Map(p1 -> 0,
                        p2 -> 0,
                        p3 -> 0,
                        p4 -> 2))

    analyze_all(pn, m, "B1")
  }


  // Beispiel 2
  {
    val p1 = Place("p1", 1)
    val p2 = Place("p2", 1)

    val t1 = Transition("t1")
    val t2 = Transition("t2")

    val pn = PetriNet(Set(p1, p2),
                      Set(t1, t2),
                      Set(Edge(p1,t1),
                          Edge(t1,p2),
                          Edge(p2,t2),
                          Edge(t2,p1)))

    val m = Marking(pn,
                    Map(p1 -> 1,
                        p2 -> 0))

    analyze_all(pn, m, "B2")
  }

  // Beispiel 3
  {
    val p1 = Place("p1", 1)
    val p2 = Place("p2", 1)
    val p3 = Place("p3", 1)

    val t1 = Transition("t1")
    val t2 = Transition("t2")
    val t3 = Transition("t3")

    val pn = PetriNet(Set(p1, p2, p3),
                      Set(t1, t2, t3),
                      Set(Edge(p1,t1),
                          Edge(t1,p2),
                          Edge(p2,t2),
                          Edge(t2,p1),
                          Edge(p2,t3)))

    val m = Marking(pn,
                    Map(p1 -> 1,
                        p2 -> 0, p3 -> 0))
    analyze_all(pn, m, "B3")
  }



  // Beispiel 4
  {
    val p1 = Place("p1", 1)
    val p2 = Place("p2", 1)
    val p3 = Place("p3", 1)
    val p4 = Place("p4", 1)

    val t1 = Transition("t1")
    val t2 = Transition("t2")
    val t3 = Transition("t3")

    val pn = PetriNet(Set(p1, p2, p3, p4),
                      Set(t1, t2, t3),
                      Set(Edge(p1,t1),
                          Edge(t1,p2),
                          Edge(p2,t2),
                          Edge(t2,p1),
                          Edge(t2,p3),
                          Edge(p3,t3),
                          Edge(t3,p4),
                          Edge(p4,t2)))

    val m = Marking(pn,
                    Map(p1 -> 1,
                        p2 -> 0, 
						p3 -> 1, 
						p4 -> 0))

    analyze_all(pn, m, "B4")
  }

}


object PrintDot extends App {


  val p1 = Place("p1", 1000)
  val p2 = Place("p2", 1000)
  val p3 = Place("p3", 1)
  val p4 = Place("p4", 1000)

  val t1 = Transition("t1")
  val t2 = Transition("t2")
  val t3 = Transition("t3")

  val pn = PetriNet(Set(p1, p2, p3, p4),
                    Set(t1, t2, t3),
                    Set(Edge(t1,p1,1),
                        Edge(t1,p2,1),
                        Edge(p1,t2,1),
                        Edge(p2,t3,1),
                        Edge(t2,p3,1),
                        Edge(t2,p4,1),
                        Edge(t3,p4,1),
                        Edge(p4,t1,2)))

  pn printDot
}
