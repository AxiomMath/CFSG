module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLD6Axes

public section

namespace CFSG.StandardType.QTwoD6

open Module

theorem w6_normalizer_normal_form (T : V7 ≃ₗ[ZMod 3] V7)
    (hT : ∀ g : V7 ≃ₗ[ZMod 3] V7, g ∈ W6 ↔ T * g * T⁻¹ ∈ W6)
    (hT0 : T e0 ∈ Submodule.span (ZMod 3) {e0}) :
    ∃ w ∈ W6, ∃ π : Fin 6 ≃ Fin 6, (π = Equiv.refl _ ∨ π = swapD6) ∧
      ∀ i, T (hvec i) = w (hvec (π i)) := by
  choose b t ht hTa using axis_of_normalizer T hT hT0
  have hdist : ∀ a a' : Fin 6, a ≠ a' → epsVec a ≠ epsVec a' ∧ epsVec a ≠ -epsVec a' := by
    decide
  have hinj : Function.Injective b := by
    intro a a' hab
    by_contra hne
    have h1 : T (t a' • epsVec a - t a • epsVec a') = 0 := by
      rw [map_sub, map_smul, map_smul, hTa a, hTa a', hab, smul_smul, smul_smul, mul_comm,
        sub_self]
    have h2 : t a' • epsVec a = t a • epsVec a' := sub_eq_zero.mp (T.map_eq_zero_iff.mp h1)
    rcases ht a with ha | ha <;> rcases ht a' with ha' | ha' <;> rw [ha, ha'] at h2 <;>
      simp only [one_smul, neg_smul] at h2
    · exact (hdist a a' hne).1 h2
    · exact (hdist a a' hne).2 (neg_eq_iff_eq_neg.mp h2)
    · exact (hdist a a' hne).2 (by simpa using h2)
    · exact (hdist a a' hne).1 (neg_inj.mp h2)
  exact monomial_normal_form T (Equiv.ofBijective b (Finite.injective_iff_bijective.mp hinj)) t
    ht hT0 hTa

end CFSG.StandardType.QTwoD6

end
