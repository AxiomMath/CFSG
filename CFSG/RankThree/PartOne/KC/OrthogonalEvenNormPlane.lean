module

public import CFSG.LocalAnalysis.SteinbergCEAnisotropicNormIsometry
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module

structure EvenNormPlane (K E : Type) [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] where
  σ : E ≃ₐ[K] E
  finrank_eq : finrank K E = 2
  σ_ne_one : σ ≠ 1
  N : QuadraticForm K E
  algebraMap_N : ∀ z, algebraMap K E (N z) = z * σ z

theorem charP_two_of_algebra {K E : Type} [Field K] [CharP K 2] [Field E] [Algebra K E] :
    CharP E 2 :=
  charP_of_injective_algebraMap (algebraMap K E).injective 2

namespace EvenNormPlane

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

include D

theorem sigma_eq_pow (z : E) : D.σ z = z ^ Nat.card K := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact CFSG.LocalAnalysis.eq_pow_card_of_ne_one D.finrank_eq D.σ_ne_one z

theorem card_E : Nat.card E = Nat.card K ^ 2 := by
  classical
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card (α := K)]
  exact CFSG.LocalAnalysis.natCard_eq_sq_of_finrank_eq_two D.finrank_eq

theorem finite_E : Finite E := by
  have : Module.Finite K E := Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)
  exact Module.finite_of_finite K


theorem sigma_sigma (z : E) : D.σ (D.σ z) = z := by
  classical
  have := D.finite_E
  have := Fintype.ofFinite E
  rw [D.sigma_eq_pow, D.sigma_eq_pow, ← pow_mul, ← sq, ← D.card_E, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card z

theorem sigma_eq_self_iff (z : E) : D.σ z = z ↔ z ∈ (algebraMap K E).range := by
  classical
  have := Fintype.ofFinite K
  rw [D.sigma_eq_pow, Nat.card_eq_fintype_card]
  exact CFSG.LocalAnalysis.pow_card_eq_self_iff D.finrank_eq z

end EvenNormPlane

end CFSG.RankThree.PartOne.KCOrthogonal
