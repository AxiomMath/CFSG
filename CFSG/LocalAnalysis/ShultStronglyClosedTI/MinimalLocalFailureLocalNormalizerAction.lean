module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalNormalizerOddJoin
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityOriginalAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowHullAction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
open CFSG.ShultStronglyClosedTI.TripleSylowMaximality

universe u

variable {G : Type u} [Group G] [Finite G]

theorem leastFailure_local_normalizer_odd_join_action
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (U : Subgroup (Subgroup.normalizer (X : Set G))) (hUodd : Odd (Nat.card U))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) :
    let Y := Subgroup.normalizer (X : Set G)
    let zY : Y := ⟨z, invariant_subgroup_mem_normalizer hXz⟩
    let L := involutionPointHull zY
    let F := L ⊔ U
    let A := (H.subgroupOf Y).subgroupOf F
    let Delta := numeratorRightOrbit H Y (rightCosetMk H 1)
    letI := numeratorRightOrbitAction H Y (rightCosetMk H 1)
    Nat.card F < Nat.card G ∧ TwoRankAtLeastTwo F ∧
      fusionStronglyEmbedded A ∧ MulAction.IsPretransitive F Delta ∧
      MulAction.IsMultiplyPretransitive F Delta 2 ∧
      (CFSG.oddCore F ≤ A) ∧
      (∀ omega : Delta, ∀ r : CFSG.oddCore F, (r.val : F) • omega = omega) := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let F := L ⊔ U
  let A := (H.subgroupOf Y).subgroupOf F
  let Delta := numeratorRightOrbit H Y (rightCosetMk H 1)
  let := numeratorRightOrbitAction H Y (rightCosetMk H 1)
  let alpha : Delta := ⟨rightCosetMk H 1, numeratorRightOrbit_base H Y _⟩
  let : Nontrivial Delta := ⟨⟨beta, alpha, fun heq => hbeta (congrArg Subtype.val heq)⟩⟩
  obtain ⟨_hproper, hcard, _hlocal, _hcentral, hnormal, hstrong, _hclass,
    hLright, _hfixedX⟩ := leastFailure_local_normalizer_hull h X hXH hXne hXz hescape
  let : L.Normal := hnormal
  have hLrank : TwoRankAtLeastTwo L := localNormalizer_internal_hull_rank_two Y z hzY hrank
  have hLtrans : MulAction.IsPretransitive L Delta := by
    constructor
    intro a b
    obtain ⟨l, hl⟩ := hLright a b
    refine ⟨l⁻¹, Subtype.ext ?_⟩
    change pointRightCosetMul H a.val (((l⁻¹ : L) : Y) : G)⁻¹ = b.val
    simpa only [Subgroup.coe_inv, inv_inv] using hl
  have hzLmem : zY ∈ L := localPointHull_distinguished_mem zY
  let zL : L := ⟨zY, hzLmem⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans
    ((Subgroup.orderOf_coe zY).symm.trans h.local_datum.distinguished_order)
  have hzunique : ∃! omega : Delta, zY • omega = omega :=
    original_class_unique_fixed_on_invariant_set h.local_datum Y Delta
      (numeratorRightOrbit_stable H Y _) zY (distinguished_mem_pointClass z)
      ⟨rightCosetMk H 1, numeratorRightOrbit_base H Y _,
        (point_right_base_fixed_iff H z).mpr h.local_datum.distinguished_mem⟩
  obtain ⟨hFstrong, hdouble⟩ := localNormalizer_normal_odd_join_strong_embedding
    L U hUodd ((H.subgroupOf Y).subgroupOf L)
    (native_strong_embedding_of_order_conditions hstrong) hLrank hLtrans zL hzL hzunique alpha
  have hstab : MulAction.stabilizer F alpha = A := by
    ext f
    rw [MulAction.mem_stabilizer_iff]
    change (⟨pointRightCosetMul H (rightCosetMk H 1) (f.val.val : G)⁻¹, _⟩ : Delta) =
      alpha ↔ (f.val.val : G) ∈ H
    rw [Subtype.ext_iff, point_right_base_fixed_iff]
    exact H.inv_mem_iff
  have hFA : fusionStronglyEmbedded A := hstab ▸ hFstrong
  have hFrank : TwoRankAtLeastTwo F := hLrank.map_of_injective
    (Subgroup.inclusion (le_sup_left : L ≤ F)) (Subgroup.inclusion_injective _)
  have hFtrans : MulAction.IsPretransitive F Delta := normal_join_action_transitive L U hLtrans
  have hcoreA : CFSG.oddCore F ≤ A := oddCore_le_of_rank_two_stronglyEmbedded A
    (native_strong_embedding_of_order_conditions hFA) hFrank
  have hcoreH : (CFSG.oddCore F).map (Y.subtype.comp F.subtype) ≤ H := by
    rintro g ⟨r, hr, rfl⟩
    exact hcoreA hr
  have hcorefix := noncentralSylow_normal_subgroup_fixes_transitive_orbit
    (Y.subtype.comp F.subtype) H (CFSG.oddCore F) hcoreH Delta (by
      intro omega homega
      obtain ⟨l, hl⟩ := hLright alpha ⟨omega, homega⟩
      exact ⟨⟨l.val, (le_sup_left : L ≤ F) l.property⟩, hl⟩)
  refine ⟨(Subgroup.card_le_card_group F).trans_lt hcard, hFrank, hFA, hFtrans,
    hdouble, hcoreA, ?_⟩
  intro omega r
  apply Subtype.ext
  change pointRightCosetMul H omega.val (((r.val : F) : Y) : G)⁻¹ = omega.val
  exact hcorefix omega.val omega.property r.val⁻¹ ((CFSG.oddCore F).inv_mem r.property)

end CFSG.ShultStronglyClosedTI
