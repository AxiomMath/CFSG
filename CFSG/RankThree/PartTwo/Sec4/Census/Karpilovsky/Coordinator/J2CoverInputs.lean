module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2Cover

open CFSG.CosetTable CFSG.LieType.Multipliers

@[expose] def letter (z : ℤ) : Fin 2 × Bool :=
  (if z.natAbs = 1 then 0 else 1, decide (0 < z))

@[expose] def word (l : List ℤ) : List (Fin 2 × Bool) := l.map letter

@[expose] def wL : List ℤ := [1, -2, 1, -2, -2, -2, 1, 1, 1, -2]

@[expose] def j2R3 : List (Fin 2 × Bool) := word (wL ++ wL ++ wL ++ List.replicate 7 1)

@[expose] def j2Rels : List (List (Fin 2 × Bool)) :=
  [word [1, 2, 1, -2, -1, -2], word [1, 2, 2, 1, -2, -2, -2, -2, -2], j2R3]

@[expose] def j2Comm : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 => [(word [-1, 2], word [1, -2])]
  | 1 => [(word [-2, 1], word [2, -1])]

@[expose] def j2CommWord (i : Fin 2) : List (Fin 2 × Bool) := commWords (j2Comm i)

@[expose] def j2Cover : List (List (Fin 2 × Bool)) := coverWords j2Rels j2CommWord

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2Cover
