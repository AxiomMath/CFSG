module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownInputsDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE8F
  TableBExc.E6Three NoOffRest
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (e6LineChar e6LineRoots e6KacNode
  e6LineChar_kacNode e6LineChar_of_ne e6Line_kernel)

@[expose] def ggE6IsoBase : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 0, 1, 0, 0]

private abbrev isoNorm (x : Fin Tag.E6.rank → ZMod 3) : ZMod 3 :=
  E6Dep.norm6 (E6Dep.coordF.mulVec x)

private def isoBaseOne : Fin Tag.E6.rank → ZMod 3 := ![0, 1, 0, 0, 0, 0]

private def isoBaseTwo : Fin Tag.E6.rank → ZMod 3 := ![1, 0, 0, 0, 0, 1]

private def isoTabZero : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)) :=
  ([(![0, 0, 0, 1, 0, 0], []), (![0, 0, 0, 2, 0, 0], [3, 2, 0, 4, 3, 2, 5, 4, 3]),
     (![0, 0, 1, 0, 1, 0], [3, 2, 0, 4, 3, 1, 2, 3, 4]),
     (![0, 0, 1, 1, 0, 2], [3, 2, 0, 4, 3, 1, 2, 3, 5]),
     (![0, 0, 1, 1, 2, 1], [3, 2, 0, 4, 3, 1, 2, 3]), (![0, 0, 2, 0, 2, 0], [3, 1, 2, 0, 3, 2]),
     (![0, 0, 2, 2, 0, 1], [3, 1, 4, 3]), (![0, 0, 2, 2, 1, 2], [3, 1, 4, 3, 5]),
     (![0, 1, 1, 0, 0, 2], [3, 4, 5]), (![0, 1, 1, 0, 2, 1], [3, 4]), (![0, 1, 1, 2, 1, 0], [3]),
     (![0, 1, 2, 0, 2, 0], [3, 2, 0, 4, 3, 1, 2, 5, 4]),
     (![0, 1, 2, 2, 0, 1], [3, 2, 0, 4, 3, 1, 2]), (![0, 1, 2, 2, 1, 2], [3, 2, 0, 4, 3, 1, 2, 5]),
     (![0, 2, 1, 0, 1, 0], [3, 1]), (![0, 2, 1, 1, 0, 2], [3, 1, 4, 5]),
     (![0, 2, 1, 1, 2, 1], [3, 1, 4]), (![0, 2, 2, 0, 0, 1], [3, 2, 0, 4, 3, 2]),
     (![0, 2, 2, 0, 1, 2], [3, 2, 0, 4, 3, 2, 5]), (![0, 2, 2, 1, 2, 0], [3, 2, 0, 4, 3, 2, 5, 4]),
     (![1, 0, 0, 1, 0, 1], [3, 1, 2, 3, 4, 5]), (![1, 0, 0, 1, 1, 2], [3, 1, 2, 3, 4]),
     (![1, 0, 0, 2, 2, 0], [3, 1, 2, 3]), (![1, 0, 2, 1, 1, 0], [3, 2, 4, 3, 1, 5, 4, 3]),
     (![1, 0, 2, 2, 0, 2], [3, 1, 2, 0, 4, 3, 1, 2, 3, 5]),
     (![1, 0, 2, 2, 2, 1], [3, 1, 2, 0, 4, 3, 1, 2, 3]), (![1, 1, 0, 1, 0, 1], [3, 2, 4, 3, 1]),
     (![1, 1, 0, 1, 1, 2], [3, 2, 4, 3, 1, 5]), (![1, 1, 0, 2, 2, 0], [3, 2, 4, 3, 1, 5, 4]),
     (![1, 1, 1, 0, 1, 1], [3, 1, 2, 0, 4, 3, 2]), (![1, 1, 1, 0, 2, 2], [3, 1, 2, 0, 4, 3, 2, 5]),
     (![1, 1, 1, 1, 1, 1], [3, 1, 2, 4, 3]), (![1, 1, 1, 1, 2, 2], [3, 1, 2, 4, 3, 5]),
     (![1, 1, 1, 2, 1, 1], [3, 1, 2, 3, 4, 3, 5]), (![1, 1, 1, 2, 2, 2], [3, 1, 2, 3, 4, 3]),
     (![1, 1, 2, 0, 1, 0], [3, 2]), (![1, 1, 2, 1, 0, 2], [3, 2, 4, 5]),
     (![1, 1, 2, 1, 2, 1], [3, 2, 4]), (![1, 2, 0, 0, 2, 0], [3, 2, 4, 3, 5, 4]),
     (![1, 2, 0, 2, 0, 1], [3, 2, 4, 3]), (![1, 2, 0, 2, 1, 2], [3, 2, 4, 3, 5]),
     (![1, 2, 1, 0, 1, 1], [3, 1, 2, 3, 4, 3, 1, 5]), (![1, 2, 1, 0, 2, 2], [3, 1, 2, 3, 4, 3, 1]),
     (![1, 2, 1, 1, 1, 1], [3, 1, 2, 0, 4, 3, 1, 2]),
     (![1, 2, 1, 1, 2, 2], [3, 1, 2, 0, 4, 3, 1, 2, 5]), (![1, 2, 1, 2, 1, 1], [3, 1, 2, 4, 3, 1]),
     (![1, 2, 1, 2, 2, 2], [3, 1, 2, 4, 3, 1, 5]), (![1, 2, 2, 1, 1, 0], [3, 1, 2]),
     (![1, 2, 2, 2, 0, 2], [3, 1, 2, 4, 5]), (![1, 2, 2, 2, 2, 1], [3, 1, 2, 4]),
     (![2, 0, 0, 1, 1, 0], [3, 2, 0, 4, 3, 1, 5, 4, 3]),
     (![2, 0, 0, 2, 0, 2], [3, 1, 2, 3, 4, 3, 1, 2, 3]),
     (![2, 0, 0, 2, 2, 1], [3, 1, 2, 0, 4, 3, 1, 2, 0, 3]), (![2, 0, 1, 1, 0, 1], [3, 1, 4, 3, 2]),
     (![2, 0, 1, 1, 1, 2], [3, 1, 2, 0, 3, 4]), (![2, 0, 1, 2, 2, 0], [3, 1, 2, 0, 3]),
     (![2, 1, 0, 0, 1, 0], [3, 2, 0]), (![2, 1, 0, 1, 0, 2], [3, 2, 0, 4, 5]),
     (![2, 1, 0, 1, 2, 1], [3, 2, 0, 4]), (![2, 1, 1, 1, 0, 1], [3, 2, 0, 4, 3, 1]),
     (![2, 1, 1, 1, 1, 2], [3, 2, 0, 4, 3, 1, 5]), (![2, 1, 1, 2, 2, 0], [3, 2, 0, 4, 3, 1, 5, 4]),
     (![2, 1, 2, 0, 1, 1], [3, 1, 2, 0, 4, 3, 2, 0]), (![2, 1, 2, 0, 2, 2], [3, 1, 2, 3, 4, 3, 2]),
     (![2, 1, 2, 1, 1, 1], [3, 1, 2, 0, 4, 3]), (![2, 1, 2, 1, 2, 2], [3, 1, 2, 0, 4, 3, 5]),
     (![2, 1, 2, 2, 1, 1], [3, 1, 2, 4, 3, 2]), (![2, 1, 2, 2, 2, 2], [3, 1, 2, 0, 3, 4, 3]),
     (![2, 2, 0, 1, 1, 0], [3, 1, 2, 0]), (![2, 2, 0, 2, 0, 2], [3, 1, 2, 0, 4, 5]),
     (![2, 2, 0, 2, 2, 1], [3, 1, 2, 0, 4]), (![2, 2, 1, 0, 2, 0], [3, 2, 0, 4, 3, 5, 4]),
     (![2, 2, 1, 2, 0, 1], [3, 2, 0, 4, 3]), (![2, 2, 1, 2, 1, 2], [3, 2, 0, 4, 3, 5]),
     (![2, 2, 2, 0, 1, 1], [3, 1, 2, 4, 3, 1, 2]), (![2, 2, 2, 0, 2, 2], [3, 1, 2, 0, 3, 4, 3, 1]),
     (![2, 2, 2, 1, 1, 1], [3, 1, 2, 0, 4, 3, 1, 2, 0]),
     (![2, 2, 2, 1, 2, 2], [3, 1, 2, 3, 4, 3, 1, 2]), (![2, 2, 2, 2, 1, 1], [3, 1, 2, 0, 4, 3, 1]),
     (![2, 2, 2, 2, 2, 2], [3, 1, 2, 0, 4, 3, 1, 5])] :
    List ((Fin 6 → ZMod 3) × List (Fin 6)))

private def isoTabOne : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)) :=
  ([(![0, 0, 0, 0, 1, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5]),
     (![0, 0, 0, 0, 2, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4]),
     (![0, 0, 0, 1, 1, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4]),
     (![0, 0, 0, 1, 2, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4]),
     (![0, 0, 0, 2, 1, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3]),
     (![0, 0, 0, 2, 2, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5]), (![0, 0, 1, 0, 0, 2], [1, 3, 4, 5]),
     (![0, 0, 1, 0, 2, 1], [1, 3, 4]), (![0, 0, 1, 2, 1, 0], [1, 3]),
     (![0, 0, 2, 0, 0, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3, 2]),
     (![0, 0, 2, 0, 1, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2]),
     (![0, 0, 2, 1, 2, 0], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4]),
     (![0, 1, 0, 0, 0, 0], []), (![0, 1, 0, 1, 0, 0], [1, 3, 2, 0, 4, 3, 2, 5, 4, 3, 1]),
     (![0, 1, 0, 2, 0, 0], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3]),
     (![0, 1, 1, 1, 1, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3]),
     (![0, 1, 1, 2, 0, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3]),
     (![0, 1, 1, 2, 2, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3]),
     (![0, 1, 2, 0, 0, 1], [1, 3, 2, 0, 4, 3, 2]), (![0, 1, 2, 0, 1, 2], [1, 3, 2, 0, 4, 3, 2, 5]),
     (![0, 1, 2, 1, 2, 0], [1, 3, 2, 0, 4, 3, 2, 5, 4]),
     (![0, 2, 0, 0, 0, 0], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1]),
     (![0, 2, 0, 1, 0, 0], [1]), (![0, 2, 0, 2, 0, 0], [1, 3, 2, 0, 4, 3, 2, 5, 4, 3]),
     (![0, 2, 1, 0, 0, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1]),
     (![0, 2, 1, 0, 2, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1]),
     (![0, 2, 1, 2, 1, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1]),
     (![0, 2, 2, 1, 0, 1], [1, 3, 2, 0, 4, 3, 1, 2]),
     (![0, 2, 2, 1, 1, 2], [1, 3, 2, 0, 4, 3, 1, 2, 5]),
     (![0, 2, 2, 2, 2, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4]),
     (![1, 0, 0, 0, 2, 0], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 3, 4]),
     (![1, 0, 0, 2, 0, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 3]),
     (![1, 0, 0, 2, 1, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 3]),
     (![1, 0, 1, 0, 0, 0], [1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0]),
     (![1, 0, 1, 1, 0, 0], [1, 3, 2, 0, 4, 3, 1, 5, 4, 3, 2]),
     (![1, 0, 1, 2, 0, 0], [1, 3, 2, 4, 3, 1, 5, 4, 3]), (![1, 0, 2, 0, 1, 0], [1, 3, 2]),
     (![1, 0, 2, 1, 0, 2], [1, 3, 2, 4, 5]), (![1, 0, 2, 1, 2, 1], [1, 3, 2, 4]),
     (![1, 1, 0, 0, 2, 0], [1, 3, 2, 4, 3, 5, 4]), (![1, 1, 0, 2, 0, 1], [1, 3, 2, 4, 3]),
     (![1, 1, 0, 2, 1, 2], [1, 3, 2, 4, 3, 5]),
     (![1, 1, 2, 0, 0, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2]),
     (![1, 1, 2, 0, 2, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 2]),
     (![1, 1, 2, 2, 1, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 2]),
     (![1, 2, 0, 0, 0, 1], [1, 3, 2, 4, 3, 1]), (![1, 2, 0, 0, 1, 2], [1, 3, 2, 4, 3, 1, 5]),
     (![1, 2, 0, 1, 2, 0], [1, 3, 2, 4, 3, 1, 5, 4]),
     (![1, 2, 2, 0, 1, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1, 2]),
     (![1, 2, 2, 1, 0, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2]),
     (![1, 2, 2, 1, 2, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2]),
     (![2, 0, 0, 0, 1, 0], [1, 3, 2, 0]), (![2, 0, 0, 1, 0, 2], [1, 3, 2, 0, 4, 5]),
     (![2, 0, 0, 1, 2, 1], [1, 3, 2, 0, 4]),
     (![2, 0, 1, 0, 2, 0], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3, 4]),
     (![2, 0, 1, 2, 0, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3]),
     (![2, 0, 1, 2, 1, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3]),
     (![2, 0, 2, 0, 0, 0], [1, 3, 2, 4, 3, 1, 5, 4, 3, 2]),
     (![2, 0, 2, 1, 0, 0], [1, 3, 2, 0, 4, 3, 1, 5, 4, 3, 2, 0]),
     (![2, 0, 2, 2, 0, 0], [1, 3, 2, 0, 4, 3, 1, 5, 4, 3]),
     (![2, 1, 0, 0, 0, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 0]),
     (![2, 1, 0, 0, 2, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 2, 0]),
     (![2, 1, 0, 2, 1, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 2, 0]),
     (![2, 1, 1, 0, 2, 0], [1, 3, 2, 0, 4, 3, 5, 4]), (![2, 1, 1, 2, 0, 1], [1, 3, 2, 0, 4, 3]),
     (![2, 1, 1, 2, 1, 2], [1, 3, 2, 0, 4, 3, 5]),
     (![2, 2, 0, 0, 1, 0], [1, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1, 2, 0]),
     (![2, 2, 0, 1, 0, 2], [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 0]),
     (![2, 2, 0, 1, 2, 1], [1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0]),
     (![2, 2, 1, 0, 0, 1], [1, 3, 2, 0, 4, 3, 1]), (![2, 2, 1, 0, 1, 2], [1, 3, 2, 0, 4, 3, 1, 5]),
     (![2, 2, 1, 1, 2, 0], [1, 3, 2, 0, 4, 3, 1, 5, 4])] :
    List ((Fin 6 → ZMod 3) × List (Fin 6)))

private def isoTabTwo : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank)) :=
  ([(![0, 0, 1, 1, 1, 0], [0, 2, 3, 1, 4, 3, 5, 4]), (![0, 0, 1, 2, 0, 2], [0, 2, 3, 1, 4, 3]),
     (![0, 0, 1, 2, 2, 1], [0, 2, 3, 1, 4, 3, 5]), (![0, 0, 2, 1, 0, 1], [0, 2]),
     (![0, 0, 2, 1, 1, 2], [0, 2, 5]), (![0, 0, 2, 2, 2, 0], [0, 2, 5, 4]),
     (![0, 1, 0, 0, 1, 1], [0, 2, 3, 4, 5]), (![0, 1, 0, 0, 2, 2], [0, 2, 3, 4]),
     (![0, 1, 0, 1, 1, 1], [0, 2, 3, 5, 4]), (![0, 1, 0, 1, 2, 2], [0, 2, 3, 4, 5, 4]),
     (![0, 1, 0, 2, 1, 1], [0, 2, 3]), (![0, 1, 0, 2, 2, 2], [0, 2, 3, 5]),
     (![0, 1, 1, 0, 1, 0], [0, 2, 5, 4, 3, 1]), (![0, 1, 1, 1, 0, 2], [0, 2, 3, 4, 5, 4, 3, 1]),
     (![0, 1, 1, 1, 2, 1], [0, 2, 3, 5, 4, 3, 1]), (![0, 1, 2, 1, 0, 1], [0, 2, 3, 1, 5, 4, 3]),
     (![0, 1, 2, 1, 1, 2], [0, 2, 3, 1, 4, 5, 4, 3]),
     (![0, 1, 2, 2, 2, 0], [0, 2, 3, 1, 4, 3, 5, 4, 3]), (![0, 2, 0, 0, 1, 1], [0, 2, 3, 1]),
     (![0, 2, 0, 0, 2, 2], [0, 2, 3, 1, 5]), (![0, 2, 0, 1, 1, 1], [0, 2, 3, 1, 4, 5]),
     (![0, 2, 0, 1, 2, 2], [0, 2, 3, 1, 4]), (![0, 2, 0, 2, 1, 1], [0, 2, 3, 1, 5, 4]),
     (![0, 2, 0, 2, 2, 2], [0, 2, 3, 1, 4, 5, 4]), (![0, 2, 1, 1, 1, 0], [0, 2, 5, 4, 3]),
     (![0, 2, 1, 2, 0, 2], [0, 2, 3, 4, 5, 4, 3]), (![0, 2, 1, 2, 2, 1], [0, 2, 3, 5, 4, 3]),
     (![0, 2, 2, 0, 2, 0], [0, 2, 3, 1, 4, 3, 5, 4, 3, 1]),
     (![0, 2, 2, 2, 0, 1], [0, 2, 3, 1, 5, 4, 3, 1]),
     (![0, 2, 2, 2, 1, 2], [0, 2, 3, 1, 4, 5, 4, 3, 1]), (![1, 0, 0, 0, 0, 1], []),
     (![1, 0, 0, 0, 1, 2], [5]), (![1, 0, 0, 1, 2, 0], [5, 4]),
     (![1, 0, 1, 0, 1, 1], [0, 2, 3, 4, 5, 4, 3, 1, 2, 3, 4]),
     (![1, 0, 1, 0, 2, 2], [0, 2, 3, 1, 5, 4, 3, 1, 2, 0, 3, 4]),
     (![1, 0, 1, 1, 1, 1], [0, 2, 3, 5, 4, 3, 1, 2, 3]),
     (![1, 0, 1, 1, 2, 2], [0, 2, 3, 4, 5, 4, 3, 1, 2, 3]),
     (![1, 0, 1, 2, 1, 1], [0, 2, 3, 1, 5, 4, 3, 1, 2, 0, 3]),
     (![1, 0, 1, 2, 2, 2], [0, 2, 3, 5, 4, 3, 1, 2, 3, 4]),
     (![1, 0, 2, 0, 0, 2], [0, 2, 3, 1, 4, 3, 2]), (![1, 0, 2, 0, 2, 1], [0, 2, 3, 1, 4, 3, 2, 5]),
     (![1, 0, 2, 2, 1, 0], [5, 4, 3, 1, 2, 0, 3]),
     (![1, 1, 0, 0, 0, 1], [0, 2, 3, 1, 5, 4, 3, 2, 0]),
     (![1, 1, 0, 0, 1, 2], [0, 5, 4, 3, 1, 2, 3, 4]), (![1, 1, 0, 1, 2, 0], [0, 5, 4, 3, 1, 2, 3]),
     (![1, 1, 1, 0, 0, 0], [5, 4, 3, 2, 0]), (![1, 1, 1, 1, 0, 0], [0, 5, 4, 3, 2]),
     (![1, 1, 1, 2, 0, 0], [5, 4, 3]), (![1, 1, 2, 1, 1, 0], [0, 2, 5, 4, 3, 1, 2]),
     (![1, 1, 2, 2, 0, 2], [0, 2, 3, 4, 5, 4, 3, 1, 2]),
     (![1, 1, 2, 2, 2, 1], [0, 2, 3, 5, 4, 3, 1, 2]),
     (![1, 2, 0, 1, 0, 1], [0, 2, 3, 1, 5, 4, 3, 1, 2, 0]),
     (![1, 2, 0, 1, 1, 2], [0, 2, 5, 4, 3, 1, 2, 3, 4]),
     (![1, 2, 0, 2, 2, 0], [0, 2, 5, 4, 3, 1, 2, 3]), (![1, 2, 1, 0, 0, 0], [5, 4, 3, 1]),
     (![1, 2, 1, 1, 0, 0], [5, 4, 3, 1, 2, 0]), (![1, 2, 1, 2, 0, 0], [0, 5, 4, 3, 1, 2]),
     (![1, 2, 2, 0, 0, 2], [0, 2, 3, 4, 5, 4, 3, 2]), (![1, 2, 2, 0, 2, 1], [0, 2, 3, 5, 4, 3, 2]),
     (![1, 2, 2, 2, 1, 0], [0, 2, 5, 4, 3, 2]), (![2, 0, 0, 0, 0, 2], [0, 2, 3, 1, 4, 3, 2, 0]),
     (![2, 0, 0, 0, 2, 1], [5, 4, 3, 1, 2, 3, 4]), (![2, 0, 0, 2, 1, 0], [5, 4, 3, 1, 2, 3]),
     (![2, 0, 1, 0, 0, 1], [0]), (![2, 0, 1, 0, 1, 2], [0, 5]), (![2, 0, 1, 1, 2, 0], [0, 5, 4]),
     (![2, 0, 2, 0, 1, 1], [0, 2, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2]),
     (![2, 0, 2, 0, 2, 2], [0, 2, 3, 1, 5, 4, 3, 1, 2, 3, 4]),
     (![2, 0, 2, 1, 1, 1], [0, 2, 3, 5, 4, 3, 1, 2, 0, 3]),
     (![2, 0, 2, 1, 2, 2], [0, 2, 3, 4, 5, 4, 3, 1, 2, 0, 3]),
     (![2, 0, 2, 2, 1, 1], [0, 2, 3, 1, 5, 4, 3, 1, 2, 3]),
     (![2, 0, 2, 2, 2, 2], [0, 2, 3, 1, 4, 5, 4, 3, 1, 2, 3]),
     (![2, 1, 0, 1, 1, 0], [0, 2, 5, 4, 3, 1, 2, 0]),
     (![2, 1, 0, 2, 0, 2], [0, 2, 3, 4, 5, 4, 3, 1, 2, 0]),
     (![2, 1, 0, 2, 2, 1], [0, 2, 3, 5, 4, 3, 1, 2, 0]),
     (![2, 1, 1, 0, 0, 1], [0, 2, 3, 1, 5, 4, 3, 2]),
     (![2, 1, 1, 0, 1, 2], [0, 2, 3, 1, 4, 5, 4, 3, 2]),
     (![2, 1, 1, 1, 2, 0], [0, 5, 4, 3, 1, 2, 0, 3]), (![2, 1, 2, 0, 0, 0], [5, 4, 3, 2]),
     (![2, 1, 2, 1, 0, 0], [0, 5, 4, 3, 2, 0]), (![2, 1, 2, 2, 0, 0], [0, 5, 4, 3]),
     (![2, 2, 0, 0, 0, 2], [0, 2, 3, 4, 5, 4, 3, 2, 0]),
     (![2, 2, 0, 0, 2, 1], [0, 2, 3, 5, 4, 3, 2, 0]), (![2, 2, 0, 2, 1, 0], [0, 2, 5, 4, 3, 2, 0]),
     (![2, 2, 1, 1, 0, 1], [0, 2, 3, 1, 5, 4, 3, 1, 2]),
     (![2, 2, 1, 1, 1, 2], [0, 2, 3, 1, 4, 5, 4, 3, 1, 2]),
     (![2, 2, 1, 2, 2, 0], [0, 2, 5, 4, 3, 1, 2, 0, 3]), (![2, 2, 2, 0, 0, 0], [0, 5, 4, 3, 1]),
     (![2, 2, 2, 1, 0, 0], [5, 4, 3, 1, 2]), (![2, 2, 2, 2, 0, 0], [0, 5, 4, 3, 1, 2, 0])] :
    List ((Fin 6 → ZMod 3) × List (Fin 6)))

private theorem isoTab_acts : (∀ p ∈ isoTabZero, adWord .E6 3 p.2 p.1 = ggE6IsoBase) ∧
    (∀ p ∈ isoTabOne, adWord .E6 3 p.2 p.1 = isoBaseOne) ∧
    ∀ p ∈ isoTabTwo, adWord .E6 3 p.2 p.1 = isoBaseTwo := by
  decide +kernel

private theorem isoTab_complete : ∀ x : Fin Tag.E6.rank → ZMod 3, kDotP 3 x = 0 → x ≠ 0 →
    (isoNorm x = 0 → x ∈ isoTabZero.map Prod.fst) ∧ (isoNorm x = 1 → x ∈ isoTabOne.map Prod.fst) ∧
      (isoNorm x = 2 → x ∈ isoTabTwo.map Prod.fst) := by
  decide +kernel

private abbrev isoLevel (c : ZMod 3) : Finset (Fin Tag.E6.rank → ZMod 3) :=
  Finset.univ.filter fun x => kDotP 3 x = 0 ∧ x ≠ 0 ∧ isoNorm x = c

private theorem card_isoLevel :
    (isoLevel 0).card = 80 ∧ (isoLevel 1).card = 72 ∧ (isoLevel 2).card = 90 := by
  decide +kernel

private theorem isoNorm_adRefl : ∀ i : Fin Tag.E6.rank, ∀ x : Fin Tag.E6.rank → ZMod 3,
    kDotP 3 x = 0 → isoNorm (adRefl .E6 3 i x) = isoNorm x := by
  decide +kernel

private theorem isoNorm_adWord (ω : List (Fin Tag.E6.rank)) {x : Fin Tag.E6.rank → ZMod 3}
    (hx : kDotP 3 x = 0) : isoNorm (adWord .E6 3 ω x) = isoNorm x := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change isoNorm (adRefl .E6 3 i (adWord .E6 3 ω x)) = _
    rw [isoNorm_adRefl i _ ((kDot_adWord ω x).trans hx), ih]

private theorem isoNorm_adAct (u : WeylGroup Tag.E6) {x : Fin Tag.E6.rank → ZMod 3}
    (hx : x ∈ hypE6) : isoNorm (adAct Tag.E6 3 u x) = isoNorm x := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem Tag.E6).wordProd_surjective u
  rw [← adWord_eq_adAct]
  exact isoNorm_adWord ω (mem_hypE6.1 hx)

private theorem adAct_zero (u : WeylGroup Tag.E6) : adAct Tag.E6 3 u 0 = 0 := by
  funext i
  simp [adAct]

private theorem adAct_ne_zero (u : WeylGroup Tag.E6) {x : Fin Tag.E6.rank → ZMod 3} (hx : x ≠ 0) :
    adAct Tag.E6 3 u x ≠ 0 := by
  intro h
  apply hx
  have h' := congrArg (adAct Tag.E6 3 u⁻¹) h
  rwa [← adAct_mul, inv_mul_cancel, adAct_one, adAct_zero] at h'

private theorem exists_adAct_of_mem {T : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin Tag.E6.rank))}
    {b x : Fin Tag.E6.rank → ZMod 3} (hT : ∀ p ∈ T, adWord .E6 3 p.2 p.1 = b)
    (hx : x ∈ T.map Prod.fst) : ∃ u : WeylGroup Tag.E6, adAct Tag.E6 3 u x = b := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  refine ⟨(coxeterSystem Tag.E6).wordProd p.2, ?_⟩
  rw [← adWord_eq_adAct]
  exact hT p hp

private theorem exists_adAct_eq_of_norm_eq {x y : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6)
    (h0 : x ≠ 0) (hy : y ∈ hypE6) (hy0 : y ≠ 0) (hq : isoNorm y = isoNorm x) :
    ∃ u : WeylGroup Tag.E6, adAct Tag.E6 3 u x = y := by
  have key : ∀ b : Fin Tag.E6.rank → ZMod 3, (∃ u : WeylGroup Tag.E6, adAct Tag.E6 3 u x = b) →
      (∃ v : WeylGroup Tag.E6, adAct Tag.E6 3 v y = b) →
        ∃ w : WeylGroup Tag.E6, adAct Tag.E6 3 w x = y := by
    rintro b ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨v⁻¹ * u, ?_⟩
    rw [adAct_mul, hu, ← hv, ← adAct_mul, inv_mul_cancel, adAct_one]
  obtain ⟨h0x, h1x, h2x⟩ := isoTab_complete x (mem_hypE6.1 hx) h0
  obtain ⟨h0y, h1y, h2y⟩ := isoTab_complete y (mem_hypE6.1 hy) hy0
  obtain ⟨t0, t1, t2⟩ := isoTab_acts
  rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (isoNorm x) with h | h | h
  · exact key _ (exists_adAct_of_mem t0 (h0x h)) (exists_adAct_of_mem t0 (h0y (hq.trans h)))
  · exact key _ (exists_adAct_of_mem t1 (h1x h)) (exists_adAct_of_mem t1 (h1y (hq.trans h)))
  · exact key _ (exists_adAct_of_mem t2 (h2x h)) (exists_adAct_of_mem t2 (h2y (hq.trans h)))

theorem ggE6IsoOrbit_eq {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6) (h0 : x ≠ 0) :
    Set.range (fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u x) =
      {y | y ∈ hypE6 ∧ y ≠ 0 ∧
        E6Dep.norm6 (E6Dep.coordF.mulVec y) = E6Dep.norm6 (E6Dep.coordF.mulVec x)} := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨adAct_mem_hypE6 u hx, adAct_ne_zero u h0, isoNorm_adAct u hx⟩
  · rintro ⟨hy, hy0, hq⟩
    exact exists_adAct_eq_of_norm_eq hx h0 hy hy0 hq

theorem ggE6IsoOrbit_ncard {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6) (h0 : x ≠ 0) :
    (E6Dep.norm6 (E6Dep.coordF.mulVec x) = 0 ∧
        (Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u x).ncard = 80) ∨
      (E6Dep.norm6 (E6Dep.coordF.mulVec x) = 1 ∧
        (Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u x).ncard = 72) ∨
      (E6Dep.norm6 (E6Dep.coordF.mulVec x) = 2 ∧
        (Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u x).ncard = 90) := by
  have hset : ∀ c : ZMod 3, {y : Fin Tag.E6.rank → ZMod 3 | y ∈ hypE6 ∧ y ≠ 0 ∧
      E6Dep.norm6 (E6Dep.coordF.mulVec y) = c} = ↑(isoLevel c) := by
    intro c
    ext y
    simp [isoLevel, mem_hypE6]
  have hn : ∀ c : ZMod 3, E6Dep.norm6 (E6Dep.coordF.mulVec x) = c →
      (Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u x).ncard = (isoLevel c).card := by
    rintro c rfl
    rw [ggE6IsoOrbit_eq hx h0, hset, Set.ncard_coe_finset]
  obtain ⟨h80, h72, h90⟩ := card_isoLevel
  rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (isoNorm x) with h | h | h
  · exact Or.inl ⟨h, (hn 0 h).trans h80⟩
  · exact Or.inr (Or.inl ⟨h, (hn 1 h).trans h72⟩)
  · exact Or.inr (Or.inr ⟨h, (hn 2 h).trans h90⟩)

theorem ggE6IsoOrbit_ncard_eq_eighty_iff {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ hypE6)
    (h0 : x ≠ 0) :
    (Set.range fun u : WeylGroup Tag.E6 => adAct Tag.E6 3 u x).ncard = 80 ↔ GGE6IsoPt x := by
  rcases ggE6IsoOrbit_ncard hx h0 with ⟨hq, hn⟩ | ⟨hq, hn⟩ | ⟨hq, hn⟩
  · exact ⟨fun _ => ⟨hx, h0, hq⟩, fun _ => hn⟩
  · rw [hn]
    exact ⟨fun h => absurd h (by decide), fun h => absurd (h.2.2.symm.trans hq) (by decide)⟩
  · rw [hn]
    exact ⟨fun h => absurd h (by decide), fun h => absurd (h.2.2.symm.trans hq) (by decide)⟩

theorem exists_adAct_eq_ggE6IsoBase {x : Fin Tag.E6.rank → ZMod 3} (hx : GGE6IsoPt x) :
    ∃ u : WeylGroup Tag.E6, adAct Tag.E6 3 u x = ggE6IsoBase := by
  obtain ⟨hxH, hx0, hq⟩ := hx
  exact exists_adAct_of_mem isoTab_acts.1 ((isoTab_complete x (mem_hypE6.1 hxH) hx0).1 hq)

private theorem ggE6IsoBase_kacNode : (ggE6IsoBase e6KacNode).val = 1 := by
  decide +kernel

private theorem ggE6IsoBase_of_ne : ∀ i : Fin Tag.E6.rank, i ≠ e6KacNode →
    (ggE6IsoBase i).val = 0 := by
  decide +kernel

theorem zetaVec_ggE6IsoBase {K : Type} [Field K] (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase = e6LineChar ζ := by
  funext i
  rw [zetaVec_apply]
  by_cases hi : i = e6KacNode
  · rw [hi, ggE6IsoBase_kacNode, pow_one, e6LineChar_kacNode]
  · rw [ggE6IsoBase_of_ne i hi, pow_zero, e6LineChar_of_ne ζ hi]

theorem famKernel_zetaVec_ggE6IsoBase {K : Type} [Field K] {ζ : Kˣ}
    (hζ : ζ ^ 3 = 1) (h1 : ζ ≠ 1) :
    famKernel {zetaVec (τ := Tag.E6) ζ hζ ggE6IsoBase} =
      ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)) := by
  rw [zetaVec_ggE6IsoBase, ← e6Line_kernel hζ h1]
  ext α
  simp [famKernel, rootCharKernel]

end CFSG.StandardType

end
