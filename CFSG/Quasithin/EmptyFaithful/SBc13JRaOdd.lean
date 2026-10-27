module

public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

namespace SBc13

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_conjSub_eq_self {g : Γ} {J : Subgroup Γ} (h : conjSub g J = J) :
    g ∈ Subgroup.normalizer (J : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : g * x * g⁻¹ ∈ conjSub g J := mul_mem_conjSub hx
    rwa [h] at hmem
  · intro hx
    rw [← h] at hx
    simpa [mul_assoc] using mem_conjSub.mp hx

theorem conjSub_eq_self_of_mem_normalizer {g : Γ} {J : Subgroup Γ}
    (hg : g ∈ Subgroup.normalizer (J : Set Γ)) : conjSub g J = J := by
  ext x
  rw [mem_conjSub]
  simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).symm

theorem mem_of_mul_self_mem_of_odd {N : Subgroup Γ} {y : Γ} (hy : Odd (orderOf y))
    (hsq : y * y ∈ N) : y ∈ N := by
  obtain ⟨m, hm⟩ := hy
  have hone : y ^ (2 * m + 1) = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one y
  have hpow : (y * y) ^ (m + 1) = y := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hone, one_mul]
  rw [← hpow]
  exact N.pow_mem hsq (m + 1)

theorem mem_normalizer_of_odd_of_two_conjugates {J : Subgroup Γ} {t : Γ}
    (ht : t ∉ Subgroup.normalizer (J : Set Γ))
    (hz : ∀ z : Γ, conjSub z J = J ∨ conjSub z J = conjSub t J) {y : Γ}
    (hy : Odd (orderOf y)) : y ∈ Subgroup.normalizer (J : Set Γ) := by
  rcases hz y with h1 | h1
  · exact mem_normalizer_of_conjSub_eq_self h1
  · refine mem_of_mul_self_mem_of_odd hy (mem_normalizer_of_conjSub_eq_self ?_)
    rcases hz (y * t) with h2 | h2
    · rw [conjSub_mul, h1, ← conjSub_mul]
      exact h2
    · exfalso
      rw [conjSub_mul, ← h1, conjSub_inj] at h2
      exact ht (mem_normalizer_of_conjSub_eq_self (h1.symm.trans h2))

end SBc13

end CFSG.Quasithin
