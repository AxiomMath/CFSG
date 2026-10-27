module

public import CFSG.Sporadic.Recognition.ONMultiplierInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.ONMultiplier
open CFSG.Sporadic.ON.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] def lowLetters (w : List (Fin 4 × Bool)) : Bool := w.all fun l => decide (l.1.val < 3)

abbrev cov : List (List (Fin 4 × Bool)) := coverWords onRels onCommWord

@[expose] def byLength (ws : List (List (Fin 4 × Bool))) : List (List (Fin 4 × Bool)) :=
  ws.mergeSort fun u v => decide (u.length ≤ v.length)

@[expose] def hatS : List (List (Fin 4 × Bool)) :=
  byLength (cov.filter lowLetters ++ [[(3, false)]])

@[expose] def rsWs : List (List (Fin 4 × Bool)) := onRels.filter lowLetters

@[expose] def mainWs : List (List (Fin 4 × Bool)) := byLength (cov ++ rsWs)

abbrev mainWs₁ := restrictWords (subsetOf 4 [0, 1, 2]) mainWs

@[expose] def alphaImgs : List (List (Fin 4 × Bool)) :=
  [[(0, true)], [(1, true), (0, true), (1, true)], [(2, true)], []]

@[expose] def zetaWord : List (Fin 4 × Bool) := ofCodes [5, 1, 5, 1, 5, 0, 2, 5, 0, 5, 0, 5, 2, 0]

@[expose] def hatWords : List (List (Fin 4 × Bool) × ℕ) :=
  (zetaWord, 3) :: (substWord alphaImgs zetaWord ++ zetaWord, 1) ::
    hatS.map fun ρ => (substWord alphaImgs ρ, 1)

@[expose] def tauWords : List (List (Fin 4 × Bool)) :=
  [ofCodes [6, 6, 0, 7, 7, 1], ofCodes [6, 6, 2, 7, 7, 3, 1, 3], ofCodes [6, 6, 4, 7, 7, 5]]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
