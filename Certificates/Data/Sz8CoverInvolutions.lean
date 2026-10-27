module

public import CFSG.LieType.Multipliers.Sz8BridgeInputs

public section

namespace CFSG.LieType.Multipliers.Sz8

@[expose] def tOne : List (Fin 2 × Bool) := parseWord "babbaBabaBabbabaBab"

@[expose] def tTwo : List (Fin 2 × Bool) := parseWord "BaBababbaBabbabaBabab"

@[expose] def centWords : List (List (Fin 2 × Bool)) :=
  [commWord tOne [(0, true)], commWord tTwo [(0, true)]]

@[expose] def invWords : List (List (Fin 2 × Bool) × ℕ) :=
  [([(0, true), (0, true)] ++ FreeGroup.invRev (parseWord relFive), 2),
    ([(0, true), (0, true)] ++ FreeGroup.invRev (parseWord relSeven), 2),
    ([(0, true), (0, true)] ++ FreeGroup.invRev (parseWord relFive ++ parseWord relSeven), 2),
    (commWord tOne [(0, true)], 2), (commWord tTwo [(0, true)], 2),
    (commWord tOne [(0, true)] ++ FreeGroup.invRev (commWord tTwo [(0, true)]), 2)]

end CFSG.LieType.Multipliers.Sz8
