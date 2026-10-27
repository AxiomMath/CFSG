module

public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruZLPos : List (ℕ × ℕ) := [(154, 19), (1471, 55), (1640, 3)]

@[expose] def ruZLA (i : ℕ) : Array ℕ :=
  prod2A 4060 ruLevL (ruZLPos.getD i (0, 0)).1 (ruZLPos.getD i (0, 0)).2

@[expose] def ruLOrbFix (t : Array ℕ) : ℕ := count2 4060 ruLevL fun l => t[l[0]!]! == l[0]!

@[expose] def ruFixCnt (t : Array ℕ) : ℕ := (fixedList 4060 t).length

@[expose] def ruLInv (t : Array ℕ) : List ℕ :=
  ruLOrbFix t :: (List.range 3).flatMap fun i =>
    [ruFixCnt (compA 4060 (ruZLA i) t),
      ruFixCnt (compA 4060 (compA 4060 (ruZLA i) t) (compA 4060 (ruZLA i) t))]

end CFSG.Sporadic.RuSchreier
