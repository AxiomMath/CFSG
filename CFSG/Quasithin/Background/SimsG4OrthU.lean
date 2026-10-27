module

public import CFSG.Quasithin.Background.SimsG4OrthUAbel

public section

namespace CFSG.Quasithin.SimsG4

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem exists_ne_zero_of_polar_nondeg [Nontrivial W] (Q : QuadraticForm K W)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) : ∃ x, Q x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  exact hx (hnd x fun y => by simp [QuadraticMap.polar, h])

section CharTwo

variable [CharP K 2]

theorem eq_one_of_mul_self_eq_one {a : K} (h : a * a = 1) : a = 1 := by
  have h2 : (a - 1) * (a - 1) = 0 := by
    linear_combination h + (1 - a) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem scalar_eq_one_of_isometry (Q : QuadraticForm K W) {x₀ : W} (hx₀ : Q x₀ ≠ 0) {a : K}
    (ha : Q (a • x₀) = Q x₀) : a = 1 := by
  rw [QuadraticMap.map_smul, smul_eq_mul] at ha
  exact eq_one_of_mul_self_eq_one (mul_right_cancel₀ hx₀ (ha.trans (one_mul _).symm))

variable [PerfectField K]

theorem false_of_abelian_odd_normal_of_isometry (Q : QuadraticForm K W)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) (hdim : 2 < Module.finrank K W)
    {G : Subgroup (W ≃ₗ[K] W)} (hprim : ¬ IsImprimitiveOnV G) {d : W ≃ₗ[K] W} (hd : d ∈ G)
    (hdt : IsTransv d) {C : Subgroup (W ≃ₗ[K] W)} (hC : C ≠ ⊥)
    (hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hCodd : ∀ c ∈ C, Odd (orderOf c))
    (hCG : ∀ g ∈ G, ∀ c ∈ C, g * c * g⁻¹ ∈ C) (hCQ : ∀ c ∈ C, ∀ x, Q (c x) = Q x) : False := by
  haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_polar_nondeg Q hnd
  refine false_of_abelian_odd_normal hdim hprim hd hdt hC hCcomm hCodd hCG fun c hc a hca => ?_
  have ha : a = 1 := scalar_eq_one_of_isometry Q hx₀ (by rw [← hca]; exact hCQ c hc x₀)
  exact LinearEquiv.ext fun x => by simp [hca, ha]

end CharTwo

end CFSG.Quasithin.SimsG4
