module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsRealign
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedSetup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoset

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_normalizer_aHull {z c : G} {A : Subgroup G}
    (hc : c ∈ Subgroup.centralizer (A : Set G)) :
    c ∈ Subgroup.normalizer (aHull z A : Set G) := by
  have key : ∀ g ∈ Subgroup.centralizer (A : Set G), ∀ y ∈ involutionPointClass z ∩
      (Subgroup.centralizer (A : Set G) : Set G),
      g * y * g⁻¹ ∈ involutionPointClass z ∩ (Subgroup.centralizer (A : Set G) : Set G) := by
    rintro g hg y ⟨⟨k, rfl⟩, hyA⟩
    refine ⟨⟨k * g⁻¹, ?_⟩, ?_⟩
    · simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem]
      group
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hyA) (Subgroup.inv_mem _ hg)
  have hcS : c ∈ Subgroup.normalizer
      (involutionPointClass z ∩ (Subgroup.centralizer (A : Set G) : Set G)) := by
    refine Subgroup.mem_set_normalizer_iff.mpr fun y => ⟨key c hc y, fun h => ?_⟩
    have h' := key c⁻¹ (Subgroup.inv_mem _ hc) _ h
    rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h'
  exact Subgroup.normalizer_le_normalizer_closure _ hcS

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t u : G}
  {A P : Subgroup G} (d : ExclusionSetup H z beta t u A P)

namespace ExclusionSetup

include d

theorem u_mul_self : u * u = 1 := by
  rw [← pow_two]
  exact d.u_sq

theorem u_mem_centralizer_A : u ∈ Subgroup.centralizer (A : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ ha =>
    (Subgroup.mem_centralizer_singleton_iff.mp (d.A_u ha))

theorem u_normalizes_LA : ∀ x ∈ aHull z A, u * x * u⁻¹ ∈ aHull z A := fun x hx =>
  (Subgroup.mem_normalizer_iff.mp (mem_normalizer_aHull d.u_mem_centralizer_A) x).mp hx

theorem u_commute_pairHull : ∀ x ∈ minimalLocalFailureProperPairHull H z beta t,
    u * x = x * u := fun _ hx =>
  (Subgroup.mem_centralizer_singleton_iff.mp (d.u_pairHull hx)).symm

theorem u_not_centralize_LA : ∃ x ∈ aHull z A, u * x ≠ x * u := by
  by_contra! hall
  apply d.LA_not_le
  refine le_uHull_of_le_centralizer (aHull_eq_closure z A) fun x hx => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hall x hx).symm

end ExclusionSetup

structure BarCoordinates (d : ExclusionSetup H z beta t u A P) : Type where
  φ : hermitianUnipotentCoord d.FA.J ≃* d.FA.root
  point : ∀ w, (φ w : G) ∈ minimalLocalFailurePairActionPointHull H z ↔ w.1.1 = 0
  bar : ∀ w, u * (φ w : G) * u⁻¹ = (φ (rootTau d.FA.J w) : G)

theorem ExclusionSetup.nonempty_barCoordinates [Finite G] : Nonempty (BarCoordinates d) := by
  obtain ⟨φ, hQ, hu⟩ := exists_bar_coordinates d.FA d.u_mul_self d.u_normalizes_LA
    d.u_commute_pairHull d.u_not_centralize_LA
  exact ⟨⟨φ, hQ, hu⟩⟩

namespace BarCoordinates

variable {d} (b : BarCoordinates d)

theorem bar_field (v : d.FA.root) :
    u * (v : G) * u⁻¹ = (fieldInvolution d.FA.J b.φ v : G) := by
  obtain ⟨w, rfl⟩ := b.φ.surjective v
  rw [b.bar, fieldInvolution, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

theorem center_eq : rootCenterIn d.FA.J b.φ d.FA.root.subtype =
    minimalLocalFailurePairActionPointHull H z := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, mem_rootCenter] at hv
    have h := (b.point (b.φ.symm v)).mpr hv
    rwa [MulEquiv.apply_symm_apply] at h
  · intro hx
    have hxV : x ∈ d.FA.root := le_root d.FA hx
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_rootCenter]
    refine (b.point _).mp ?_
    rwa [MulEquiv.apply_symm_apply]

theorem coset_eq : involutionCoset d.FA.J b.φ d.FA.root.subtype u =
    u • (minimalLocalFailurePairActionPointHull H z : Set G) := by
  rw [involutionCoset, b.center_eq]

end BarCoordinates

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
