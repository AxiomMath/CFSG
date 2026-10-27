
module

public import CFSG.Sporadic.Th.IndexBase1

public import CFSG.Sporadic.Th.Base

public section

namespace CFSG.Sporadic.Th

open Native Pointwise

section Facts

variable (hF : OrbitFacts)
include hF

theorem eq_one_of_idx_fix
    (hd : deltaOK thSt = true) (h124 : 124 ≤ nX) {g : J}
    (hg : ∀ j < 124, idx nX g j = j) : g = 1 := by
  apply eq_one_of_fixes_deltaPlanes g
  intro j hj
  have hjn : j < nX := lt_of_lt_of_le hj h124
  have hk : readKey thSt.keys j = deltaKeys[j]! := by
    have := (allIn_eq_true.1 hd) j (Nat.zero_le _) hj
    exact (Key.beq_iff).1 this
  have := (idx_eq_iff hF hjn hjn).1 (hg j hj)
  rw [planeAt, hk] at this
  exact this

end Facts

end CFSG.Sporadic.Th
