module

public import CFSG.RankThree.PartTwo.KFacts.KP4Data

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv

@[expose] def vElem (i : Fin 4) : Fin 4 → Perm (Fin 22) := ![1, vA i, vB i, vA i * vB i]

@[expose] def conjIdx : Fin 4 → Fin 4 → Fin 4 :=
  ![![1, 3, 3, 3], ![2, 1, 1, 1], ![3, 1, 2, 3], ![1, 2, 3, 1]]

@[expose] def lineA : Fin 4 → ℕ := ![1, 0, 1, 1]

@[expose] def lineB : Fin 4 → ℕ := ![0, 1, 1, 2]

end CFSG.RankThree.PartTwo.KFacts.KP4
