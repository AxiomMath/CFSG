module

public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.LocalAnalysis.SteinbergBK

open CFSG.OrderReductions.FrattiniAutomorphisms

section Kernels

variable {P : Type*} [Group P]

theorem isPGroup_two_of_odd_eq_one {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : ∀ σ ∈ K, Odd (orderOf σ) → σ = 1) : IsPGroup 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro σ
  obtain ⟨j, m, hm, hσ⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos σ).ne'
  refine ⟨j, ?_⟩
  have h1 : orderOf (σ ^ 2 ^ j) = m := by
    have hg : Nat.gcd (2 ^ j * m) (2 ^ j) = 2 ^ j := Nat.gcd_eq_right (dvd_mul_right _ _)
    rw [orderOf_pow' σ (by positivity), hσ, hg, Nat.mul_div_cancel_left _ (by positivity)]
  have h2 : σ ^ 2 ^ j = 1 := by
    have h3 := h ((σ : G) ^ 2 ^ j) (K.pow_mem σ.2 _) (by
      rw [← Subgroup.coe_pow, Subgroup.orderOf_coe, h1]
      exact hm)
    exact Subtype.ext (by simpa using h3)
  have h4 : orderOf (σ ^ 2 ^ j) = 1 := by rw [h2, orderOf_one]
  rw [h1] at h4
  rw [hσ, h4, mul_one]

end Kernels

end CFSG.LocalAnalysis.SteinbergBK
