module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedHull

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G] {H L : Subgroup G} {z t : G}
  {beta : rightCosetSpace H}

theorem mem_point_of_commute (hdatum : InvolutionPointLocalEmbedding H z) {x : G}
    (hx : Commute z x) : x ∈ H := by
  have hzα : rightCosetTranslate H (rightCosetMk H 1) z = rightCosetMk H 1 :=
    (translate_base_iff H z).mpr hdatum.distinguished_mem
  exact (translate_base_iff H x).mp
    (class_fixed_of_commute hdatum (distinguished_mem_pointClass z) hx hzα)

theorem fixes_flip_coset_of_commute (hdatum : InvolutionPointLocalEmbedding H z) {x : G}
    (hx : Commute (t⁻¹ * z * t) x) :
    rightCosetTranslate H (rightCosetMk H t) x = rightCosetMk H t := by
  have hsfix : rightCosetTranslate H (rightCosetMk H t) (t⁻¹ * z * t) = rightCosetMk H t := by
    rw [translate_mk_fixed_iff, show t * (t⁻¹ * z * t) * t⁻¹ = z by group]
    exact hdatum.distinguished_mem
  exact class_fixed_of_commute hdatum ⟨t, rfl⟩ hx hsfix

variable (F : UnitaryHullCoordinates H z beta t L)

omit [Finite G] in
include F in
theorem point_le_pairHull :
    minimalLocalFailurePairActionPointHull H z ≤ minimalLocalFailureProperPairHull H z beta t := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (SetLike.ext_iff.mp F.upper y).mpr hy
  exact (SetLike.ext_iff.mp F.subline _).mp ⟨x, upperRootL_le_sublineL F.hJ hx, rfl⟩

theorem mem_root_sup_hullTorus (hdatum : InvolutionPointLocalEmbedding H z)
    (hbt : beta = rightCosetMk H t) (hbeta : beta ≠ rightCosetMk H 1) (ht2 : t * t = 1)
    {x : G} (hxL : x ∈ L)
    (hxQ : x ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G)) :
    x ∈ F.root ⊔ hullTorus F := by
  have hzQ : z ∈ minimalLocalFailurePairActionPointHull H z :=
    Subgroup.subset_closure ⟨1, by simp⟩
  have hxH : x ∈ H := mem_point_of_commute hdatum (Subgroup.mem_centralizer_iff.mp hxQ z hzQ)
  have htL := flip_mem F
  set τ := F.flipElt htL
  set y := F.θ.symm ⟨x, hxL⟩
  have hyx : (F.θ y : G) = x := by rw [MulEquiv.apply_symm_apply]
  have hb : rightCosetMk H (F.θ τ : G) = beta := flip_coset F hbt
  have hbx : rightCosetMk H (F.θ (τ * y) : G) = rightCosetTranslate H beta x := by
    rw [map_mul, Subgroup.coe_mul, hyx, ← rightCosetTranslate_mk, hb]
  have hne1 : rightCosetMk H (F.θ τ : G) ≠ rightCosetMk H 1 := fun h => hbeta (hb.symm.trans h)
  have hne2 : rightCosetMk H (F.θ (τ * y) : G) ≠ rightCosetMk H 1 := by
    rw [hbx]
    intro h
    apply hbeta
    have h' := congrArg (fun ω => rightCosetTranslate H ω x⁻¹) h
    simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h'
    rw [h']
    exact (translate_base_iff H _).mpr (inv_mem hxH)
  obtain ⟨w, hw, -⟩ := F.root_regular τ (τ * y) hne1 hne2
  set r := F.rootHom w
  have hrT : r ∈ F.root := ⟨w, rfl⟩
  have hw' : rightCosetTranslate H beta r = rightCosetTranslate H beta x := by
    rw [← hbx, ← hw, hb]
  have hxrB : x * r⁻¹ ∈ pairPointStabilizer H beta := by
    refine ⟨(mem_rightCosetStabilizer_iff H _ _).mpr ((translate_base_iff H _).mpr
      (H.mul_mem hxH (H.inv_mem (F.root_le_point hrT)))),
      (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
    rw [← rightCosetTranslate_mul, ← hw', rightCosetTranslate_mul, mul_inv_cancel,
      rightCosetTranslate_one]
  have hrQ : r ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => (root_commute F hrT hq).symm
  have hxr := mem_hullTorus_of_mem_pair F hbt ht2 (L.mul_mem hxL (L.inv_mem (F.root_le hrT)))
    hxrB (Subgroup.mul_mem _ hxQ (Subgroup.inv_mem _ hrQ))
  rw [show x = x * r⁻¹ * r by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hxr) (Subgroup.mem_sup_left hrT)

theorem inf_centralizer_pairHull (hdatum : InvolutionPointLocalEmbedding H z)
    (hbt : beta = rightCosetMk H t) (ht2 : t * t = 1) :
    L ⊓ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) =
      hullTorus F := by
  apply le_antisymm
  · rintro x ⟨hxL, hxK⟩
    have hzK := minimalLocalFailureProperPair_distinguished_mem H z beta t
    have htK := minimalLocalFailureProperPair_flip_mem H z beta t
    have hxH : x ∈ H := mem_point_of_commute hdatum (Subgroup.mem_centralizer_iff.mp hxK z hzK)
    have hsK : t⁻¹ * z * t ∈ minimalLocalFailureProperPairHull H z beta t :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htK) hzK) htK
    have hxβ := fixes_flip_coset_of_commute hdatum (Subgroup.mem_centralizer_iff.mp hxK _ hsK)
    have hxB : x ∈ pairPointStabilizer H beta := by
      refine ⟨(mem_rightCosetStabilizer_iff H _ _).mpr ((translate_base_iff H x).mpr hxH),
        (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
      rw [hbt]
      exact hxβ
    have hxQ : x ∈ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        Subgroup.mem_centralizer_iff.mp hxK q (point_le_pairHull F hq)
    exact mem_hullTorus_of_mem_pair F hbt ht2 hxL hxB hxQ
  · intro x hx
    exact ⟨hullTorus_le F hx,
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hullTorus_commute F hx hy).symm⟩

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
