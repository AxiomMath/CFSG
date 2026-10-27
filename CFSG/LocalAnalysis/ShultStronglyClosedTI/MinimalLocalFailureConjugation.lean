module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeTransport

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem minimalLocalFailure_conjugate_class (z g : G) :
    involutionPointClass (rightConjugateElem z g) = involutionPointClass z :=
  pointClass_eq_of_mem ⟨g, rfl⟩

theorem minimalLocalFailure_conjugate_hull (z g : G) :
    involutionPointHull (rightConjugateElem z g) = involutionPointHull z := by
  unfold involutionPointHull
  rw [minimalLocalFailure_conjugate_class]

theorem minimalLocalFailure_point_right_conjugate (H : Subgroup G) (g : G)
    (hg : g ∈ H) : rightConjugate H g = H := by
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (H : Set G)).inv_mem (Subgroup.le_normalizer hg))

variable [Finite G]

theorem minimalLocalFailure_central_sylow_right_conjugate {z : G}
    (h : InvolutionPointCentralSylow z) (g : G) :
    InvolutionPointCentralSylow (rightConjugateElem z g) := by
  obtain ⟨S, hzS, hcenter⟩ := h
  have hcommute : ∀ s ∈ (S : Subgroup G), Commute z s := by
    intro s hs
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hcenter (⟨s, hs⟩ : (S : Subgroup G)))).symm
  obtain ⟨T, _, hzT, hcentral⟩ := CFSG.ProperTwoGeneratedCore.central_sylow_two_image
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).surjective S hzS hcommute
  have heq : (MulAut.conj g⁻¹) z = rightConjugateElem z g := by
    simp only [MulAut.conj_apply, rightConjugateElem, inv_inv]
  change (MulAut.conj g⁻¹) z ∈ (T : Subgroup G) at hzT
  change ∀ t ∈ (T : Subgroup G), Commute ((MulAut.conj g⁻¹) z) t at hcentral
  rw [heq] at hzT hcentral
  refine ⟨T, hzT, Subgroup.mem_center_iff.mpr ?_⟩
  intro t
  apply Subtype.ext
  exact (hcentral t t.property).symm.eq

theorem minimalLocalFailure_right_conjugate {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (g : G) (hg : g ∈ H) :
    MinimalInvolutionPointLocalFailure H (rightConjugateElem z g) := by
  have hlocal := local_point_datum_right_conjugate h.local_datum g
  rw [minimalLocalFailure_point_right_conjugate H g hg] at hlocal
  refine ⟨hlocal, minimalLocalFailure_central_sylow_right_conjugate h.central_sylow g,
    ?_, h.smaller⟩
  rw [minimalLocalFailure_conjugate_hull]
  exact h.failure

theorem minimalLocalFailure_at_point_class_member {H : Subgroup G} {z z₀ : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hz₀ : z₀ ∈ conjugacyWithin H z) :
    MinimalInvolutionPointLocalFailure H z₀ ∧
      involutionPointClass z₀ = involutionPointClass z ∧
      involutionPointHull z₀ = involutionPointHull z := by
  obtain ⟨g, rfl⟩ := hz₀
  exact ⟨minimalLocalFailure_right_conjugate h g g.property,
    minimalLocalFailure_conjugate_class z g, minimalLocalFailure_conjugate_hull z g⟩

end CFSG.ShultStronglyClosedTI
