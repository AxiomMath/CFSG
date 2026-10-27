module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyGeneration
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairAction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] def ProperStrongEmbeddingCommutingImages (G : Type u)
    [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, K < ⊤ → 2 ≤ twoRank K →
    ∀ M : Subgroup K, fusionStronglyEmbedded M →
      ∀ a b : K ⧸ CFSG.oddCore K,
        a ∈ M.map (QuotientGroup.mk' (CFSG.oddCore K)) → orderOf a = 2 →
        b ∈ M.map (QuotientGroup.mk' (CFSG.oddCore K)) → orderOf b = 2 → Commute a b

theorem sylowAssemblyProper_pair_hull_le_generated
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    minimalLocalFailureProperPairHull H z beta t ≤
      (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H beta := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hR := (pair_commutator_le_odd_core h.local_datum S hzS hzcenter hbeta ht).1
  rw [minimalLocalFailureProperPairHull_eq_native]
  exact sup_le le_sup_left (hR.trans le_sup_right)

theorem sylowAssemblyProper_exists_failed_pair
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hnot : ¬ BasePointPairGeneration H z) :
    ∃ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 ∧
      ∃ t ∈ rightPairFlipFiber H z beta,
        minimalLocalFailureProperPairHull H z beta t < ⊤ := by
  classical
  unfold BasePointPairGeneration at hnot
  push Not at hnot
  obtain ⟨beta, hbeta, t, ht, hproper⟩ := hnot
  exact ⟨beta, hbeta, t, ht, lt_of_le_of_lt
    (sylowAssemblyProper_pair_hull_le_generated h hbeta ht)
    (lt_of_le_of_ne le_top hproper)⟩

theorem sylowAssemblyProper_pair_hull_rank_two
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    2 ≤ twoRank (minimalLocalFailureProperPairHull H z beta t) := by
  obtain ⟨s, _, _, _, hV, hcard, hVK⟩ :=
    minimalLocalFailureProperPair_four_group h hbeta ht
  rw [CFSG.ComponentClassification.TwoRankTransport.subgroup]
  exact CFSG.ComponentClassification.TwoRankTransport.rank_le _ _
    (hVK.trans inf_le_right) hV 2 (by simpa using hcard)

theorem sylowAssemblyProper_quotient_involution_order_two
    (K : Subgroup G) {a : K} (ha : orderOf a = 2) :
    orderOf ((QuotientGroup.mk' (CFSG.oddCore K)) a) = 2 := by
  have haI : IsInvolution a :=
    ⟨(orderOf_eq_prime_iff.mp ha).2, (orderOf_eq_prime_iff.mp ha).1⟩
  have hker : Odd (Nat.card (QuotientGroup.mk' (CFSG.oddCore K)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card K
  have hi := involution_image_of_odd_kernel (QuotientGroup.mk' (CFSG.oddCore K)) hker haI
  exact orderOf_eq_prime hi.sq_eq_one hi.ne_one

theorem sylowAssemblyProper_class_commutators_le_pair_oddCore
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta := by
  let K := minimalLocalFailureProperPairHull H z beta t
  let M := H.subgroupOf K
  have hM : fusionStronglyEmbedded M :=
    minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper
  have hquot := hcomm K hproper (sylowAssemblyProper_pair_hull_rank_two h hbeta ht) M hM
  apply (minimalLocalFailureProperPairClassCommutators_normal_and_le_pair_oddCore
    h hbeta ht hproper ?_).2
  intro a b ha haorder hb hborder
  exact hquot _ _ (Subgroup.mem_map_of_mem _ ha)
    (sylowAssemblyProper_quotient_involution_order_two K haorder)
    (Subgroup.mem_map_of_mem _ hb)
    (sylowAssemblyProper_quotient_involution_order_two K hborder)

omit [Finite G] in
theorem sylowAssemblyProper_point_hull_isPGroup
    (H : Subgroup G) (z : G)
    (hQ : IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z)) :
    IsPGroup 2 (minimalLocalFailurePairActionPointHull H z) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro a
  exact ⟨1, by simpa only [pow_one] using
    (show a ^ 2 = 1 from Subtype.ext (hQ.2 a a.property))⟩

theorem sylowAssemblyProper_normal_point_two_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let Q := minimalLocalFailurePairActionPointHull H z
    Q ≤ H ∧ (Q.subgroupOf H).Normal ∧ IsElemAbelian 2 Q ∧ IsPGroup 2 Q ∧ z ∈ Q := by
  have hWJ := sylowAssemblyProper_class_commutators_le_pair_oddCore
    h hcomm hbeta ht hproper
  have haction := minimalLocalFailurePairAction h hbeta ht hproper hWJ
  have hQ : IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z) := haction.2.2.1
  refine ⟨minimalLocalFailurePairActionPointHull_le_point H h.local_datum.distinguished_mem,
    minimalLocalFailurePairActionPointHull_normal_in_point H h.local_datum.distinguished_mem,
    hQ, sylowAssemblyProper_point_hull_isPGroup H z hQ, ?_⟩
  exact Subgroup.subset_closure (show z ∈ conjugacyWithin H z from ⟨1, by simp⟩)

end CFSG.ShultStronglyClosedTI
