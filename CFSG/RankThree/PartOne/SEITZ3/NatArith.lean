module

public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartOne.SEITZ3

theorem sq_sub_one_eq_mul {x : ℕ} (hx : 1 ≤ x) : x ^ 2 - 1 = (x + 1) * (x - 1) := by
  have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  zify [hx, h1]
  ring

end CFSG.RankThree.PartOne.SEITZ3
