module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePointIndexTwo

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G]

theorem point_class_inter_eq_of_element_fusion (H : Subgroup G) (u : G) (huH : u ∈ H)
    (hfusion : ∀ g : G, rightConjugateElem u g ∈ H →
      ∃ h ∈ H, rightConjugateElem u g = rightConjugateElem u h) :
    involutionPointClass u ∩ (H : Set G) = conjugacyWithin H u := by
  ext t
  constructor
  · rintro ⟨⟨g, rfl⟩, htH⟩
    obtain ⟨h, hh, heq⟩ := hfusion g htH
    exact ⟨⟨h, hh⟩, heq.symm⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨h, rfl⟩, H.mul_mem (H.mul_mem (H.inv_mem h.property) huH) h.property⟩

theorem point_fixed_set_eq_centralizer_orbit_of_element_fusion
    (H : Subgroup G) (u : G) (huH : u ∈ H)
    (hfusion : ∀ g : G, rightConjugateElem u g ∈ H →
      ∃ h ∈ H, rightConjugateElem u g = rightConjugateElem u h) :
    {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} =
      {omega : rightCosetSpace H | ∃ c ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) c = omega} := by
  ext omega
  constructor
  · intro hfix
    obtain ⟨g, rfl⟩ := Quotient.exists_rep omega
    have huconj : u ∈ rightConjugate H g := by
      rw [← rightCosetStabilizer_mk]
      exact (mem_rightCosetStabilizer_iff H (rightCosetMk H g) u).mpr hfix
    have huginvH : rightConjugateElem u g⁻¹ ∈ H := by
      have hmem := (CFSG.ComponentClassification.AschbacherTightEmbedding.mem_rightConjugate_iff
        H g u).mp huconj
      simpa only [rightConjugateElem, inv_inv] using hmem
    obtain ⟨h, hhH, heq⟩ := hfusion g⁻¹ huginvH
    have hcentral : h * g ∈ Subgroup.centralizer ({u} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hconj : rightConjugateElem u (h * g) = u := by
        calc
          _ = rightConjugateElem (rightConjugateElem u h) g := by
            simp only [rightConjugateElem, mul_inv_rev, mul_assoc]
          _ = rightConjugateElem (rightConjugateElem u g⁻¹) g := by rw [← heq]
          _ = u := by simp only [rightConjugateElem, inv_inv, mul_assoc,
            inv_mul_cancel_left, inv_mul_cancel, mul_one]
      have hcomm := congrArg (fun t : G => (h * g) * t) hconj
      simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left] using hcomm.symm
    refine ⟨h * g, hcentral, ?_⟩
    rw [rightCosetTranslate_mk, one_mul]
    change Quotient.mk (QuotientGroup.rightRel H) (h * g) =
      Quotient.mk (QuotientGroup.rightRel H) g
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.mpr (by
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, one_mul] using H.inv_mem hhH)
  · rintro ⟨c, hc, rfl⟩
    have hbase : rightCosetTranslate H (rightCosetMk H 1) u = rightCosetMk H 1 := by
      apply (mem_rightCosetStabilizer_iff H (rightCosetMk H 1) u).mp
      rw [rightCosetStabilizer_base]
      exact huH
    have hcomm : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    change rightCosetTranslate H (rightCosetTranslate H (rightCosetMk H 1) c) u =
      rightCosetTranslate H (rightCosetMk H 1) c
    rw [rightCosetTranslate_mul, hcomm, ← rightCosetTranslate_mul, hbase]

theorem point_fixed_set_transitive_of_centralizer_orbit
    (H : Subgroup G) (u : G)
    (horbit : {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} =
      {omega : rightCosetSpace H | ∃ c ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) c = omega}) :
    ∀ alpha beta : rightCosetSpace H,
      rightCosetTranslate H alpha u = alpha →
      rightCosetTranslate H beta u = beta →
        ∃ c ∈ Subgroup.centralizer ({u} : Set G), rightCosetTranslate H alpha c = beta := by
  intro alpha beta halpha hbeta
  have ha : alpha ∈ {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} := halpha
  have hb : beta ∈ {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} := hbeta
  rw [horbit] at ha hb
  obtain ⟨a, haC, rfl⟩ := ha
  obtain ⟨b, hbC, rfl⟩ := hb
  refine ⟨a⁻¹ * b, (Subgroup.centralizer ({u} : Set G)).mul_mem
    ((Subgroup.centralizer _).inv_mem haC) hbC, ?_⟩
  rw [rightCosetTranslate_mul, mul_inv_cancel_left]

variable [Finite G]

theorem unique_central_sylow_involution_centralizers_transitive_fixed_set
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (z : G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hz : orderOf z = 2)
    (hunique : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (u : G) (huH : u ∈ H) (hu : orderOf u = 2) :
    {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} =
        {omega : rightCosetSpace H | ∃ c ∈ Subgroup.centralizer ({u} : Set G),
          rightCosetTranslate H (rightCosetMk H 1) c = omega} ∧
      (∀ alpha beta : rightCosetSpace H,
        rightCosetTranslate H alpha u = alpha →
        rightCosetTranslate H beta u = beta →
          ∃ c ∈ Subgroup.centralizer ({u} : Set G), rightCosetTranslate H alpha c = beta) ∧
      involutionPointClass u ∩ (H : Set G) = conjugacyWithin H u := by
  have hfull := unique_central_sylow_involution_full_fusion_control S H hSH z hzS hzcenter hz hunique
  have helement := element_fusion_in_overgroup_of_full_subgroup_fusion S H hSH hfull
  have hfusion : ∀ g : G, rightConjugateElem u g ∈ H →
      ∃ h ∈ H, rightConjugateElem u g = rightConjugateElem u h := by
    intro g hg
    exact helement u huH ⟨1, by simpa only [pow_one] using hu⟩ g hg
  have horbit := point_fixed_set_eq_centralizer_orbit_of_element_fusion H u huH hfusion
  exact ⟨horbit, point_fixed_set_transitive_of_centralizer_orbit H u horbit,
    point_class_inter_eq_of_element_fusion H u huH hfusion⟩

end CFSG.ShultStronglyClosedTI
