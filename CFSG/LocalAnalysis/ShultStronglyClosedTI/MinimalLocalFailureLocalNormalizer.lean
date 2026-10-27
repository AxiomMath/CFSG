module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerOrbit
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

theorem localNormalizer_proper
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≠ ⊤ := by
  intro hnormalizer
  let : X.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  have hXtop := (minimalLocalFailure_normal_eq_bot_or_top h X).resolve_left hXne
  rw [hXtop] at hXH
  exact h.local_datum.proper (top_le_iff.mp hXH)

theorem leastFailure_local_normalizer_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H) :
    let Y := Subgroup.normalizer (X : Set G)
    let zY : Y := ⟨z, invariant_subgroup_mem_normalizer hXz⟩
    let L := involutionPointHull zY
    let zL : L := ⟨zY, localPointHull_distinguished_mem zY⟩
    Y ≠ ⊤ ∧ Nat.card Y < Nat.card G ∧
      InvolutionPointLocalEmbedding (H.subgroupOf Y) zY ∧
      InvolutionPointCentralSylow zY ∧ L.Normal ∧
      fusionStronglyEmbedded ((H.subgroupOf Y).subgroupOf L) ∧
      involutionPointClass zY = L.subtype '' involutionPointClass zL ∧
      (∀ a b : numeratorRightOrbit H Y (rightCosetMk H 1),
        ∃ l : L, pointRightCosetMul H a.val (((l : Y) : G)) = b.val) ∧
      (∀ a : numeratorRightOrbit H Y (rightCosetMk H 1),
        X ≤ rightCosetStabilizer H a.val) := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  have hproper : Y ≠ ⊤ := localNormalizer_proper h X hXH hXne
  have hcard : Nat.card Y < Nat.card G := by
    simpa only [Subgroup.card_top] using
      Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)
  obtain ⟨hlocal, hcentral⟩ := involution_point_subgroup_inheritance
    h.local_datum Y hzY hescape
  have hcentralY : InvolutionPointCentralSylow zY := hcentral h.central_sylow
  have hstrong := h.smaller Y hcard (H.subgroupOf Y) zY hlocal hcentralY
  refine ⟨hproper, hcard, hlocal, hcentralY, minimalLocalFailure_hull_normal zY,
    hstrong, localPointHull_pointClass_eq_internal_class hlocal,
    localNormalizer_internal_hull_transitive_original_orbit H Y zY hlocal, ?_⟩
  rintro ⟨a, y, hy, hya⟩
  exact normalizer_orbit_stabilizer_contains hXH ⟨⟨y, hy⟩, hya⟩

theorem localNormalizer_internal_hull_rank_two
    (Y : Subgroup G) (z : G) (hzY : z ∈ Y)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin Y z))) :
    TwoRankAtLeastTwo (involutionPointHull (⟨z, hzY⟩ : Y)) := by
  rw [internal_involution_hull_rank_eq_original_class_closure Y z hzY] at hrank
  exact native_rank_two_of_two_le_twoRank hrank

end CFSG.ShultStronglyClosedTI
