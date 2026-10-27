module

public import CFSG.Quasithin.Background.HFL3Q

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem pt_mem_blkW (hK : Nat.card K = (2 ^ n) ^ 2) {v : Fin 3 → K} (hv : v 2 = 0) :
    pt hK v ∈ blkW n K := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_pt, rk1_apply, hv]

omit [CharP K 2] in
theorem pow_three_eq_one_of_four (hK : Nat.card K = (2 ^ 1) ^ 2) {x : K} (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h3 : x ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hK] at h3

end CFSG.Quasithin.H.L3Nine
