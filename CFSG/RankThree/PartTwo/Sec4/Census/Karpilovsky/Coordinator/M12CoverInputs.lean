module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12Cover

open CFSG.CosetTable CFSG.LieType.Multipliers

@[expose] def letter (z : ℤ) : Fin 2 × Bool :=
  (if z.natAbs = 1 then 0 else 1, decide (0 < z))

@[expose] def word (l : List ℤ) : List (Fin 2 × Bool) := l.map letter

@[expose] def m12Rels : List (List (Fin 2 × Bool)) :=
  [word [-2, 1, -2, 1, -2, 1], word [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2],
    word [1, 2, 2, 1, -2, 1, 1, 2, 1, 1, 2, 2]]

@[expose] def m12R3 : List (Fin 2 × Bool) := word [1, 2, 2, 1, -2, 1, 1, 2, 1, 1, 2, 2]

@[expose] def m12Comm : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool))
  | 0 => [(word [-1, -2, 1, 2], word [2, -1, -2, -2, 1, 1, -2, -1])]
  | 1 => [(word [-1, -1, -2], word [1, 1, 2, 2, 2, -1, -2, 1])]

@[expose] def m12CommWord (i : Fin 2) : List (Fin 2 × Bool) := commWords (m12Comm i)

@[expose] def m12Cover : List (List (Fin 2 × Bool)) := coverWords m12Rels m12CommWord

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12Cover
