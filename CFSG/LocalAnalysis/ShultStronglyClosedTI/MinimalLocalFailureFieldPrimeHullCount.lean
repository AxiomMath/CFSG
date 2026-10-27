module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullFull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicOddQuotientLift
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeCosets
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

universe u v

theorem isInvolution_iff_orderOf_eq_two {L : Type v} [Group L] {x : L} :
    IsInvolution x ↔ orderOf x = 2 :=
  ⟨fun hx => orderOf_eq_prime_iff.mpr ⟨hx.2, hx.1⟩,
    fun hx => ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩⟩

theorem card_involutions_map_oddCore {L : Type v} [Group L] [Finite L] (M : Subgroup L)
    (hcore : CFSG.oddCore L ≤ M) (hcentral : CFSG.oddCore L ≤ Subgroup.center L) :
    Nat.card {x : L ⧸ CFSG.oddCore L //
        x ∈ M.map (QuotientGroup.mk' (CFSG.oddCore L)) ∧ IsInvolution x} =
      Nat.card {x : L // x ∈ M ∧ IsInvolution x} := by
  let eta := QuotientGroup.mk' (CFSG.oddCore L)
  have hker : eta.ker = CFSG.oddCore L := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card eta.ker) := by
    rw [hker]
    exact CFSG.ComponentClassification.OddCore.odd_card L
  have hcentral' : eta.ker ≤ Subgroup.center L := by
    rw [hker]
    exact hcentral
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨eta x, Subgroup.mem_map_of_mem _ x.2.1,
    isInvolution_iff_orderOf_eq_two.mpr (CyclicPair.OddQuotient.map_involution eta hodd
      (isInvolution_iff_orderOf_eq_two.mp x.2.2))⟩) ⟨?_, ?_⟩
  · intro x w hxw
    apply Subtype.ext
    exact CyclicPair.OddQuotient.involution_lifts_injective eta hcentral' hodd
      (isInvolution_iff_orderOf_eq_two.mp x.2.2) (isInvolution_iff_orderOf_eq_two.mp w.2.2)
      (congrArg Subtype.val hxw)
  · rintro ⟨q, hqM, hq⟩
    obtain ⟨x, hx, hxq⟩ := CyclicPair.OddQuotient.exists_involution_lift eta
      (QuotientGroup.mk'_surjective _) hcentral' hodd (isInvolution_iff_orderOf_eq_two.mp hq)
    obtain ⟨m, hm, hmq⟩ := Subgroup.mem_map.mp hqM
    have hxm : x * m⁻¹ ∈ M := by
      apply hcore
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hxq]
      change q * (eta m)⁻¹ = 1
      rw [hmq, mul_inv_cancel]
    have hxM : x ∈ M := by
      have := M.mul_mem hxm hm
      rwa [inv_mul_cancel_right] at this
    exact ⟨⟨x, hxM, isInvolution_iff_orderOf_eq_two.mpr hx⟩, Subtype.ext hxq⟩

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem card_baseOrbit (H N : Subgroup G) :
    Nat.card (baseOrbit H N) = (H.subgroupOf N).index := by
  rw [← range_restrictedRightCosetEmbedding,
    Nat.card_range_of_injective (restrictedRightCosetEmbedding_injective H N)]
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel (H.subgroupOf N))

theorem centralizer_hull_rank_two {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {Q : Subgroup G} (hQ : IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {Y : Subgroup G} (hY : Y < ⊤) (hYH : ¬ Y ≤ H)
    {r : G} (hrQ : r ∈ Q) (hr1 : r ≠ 1) (hrY : r ∈ Y)
    {E : Subgroup G} (hEQ : E ≤ Q) (hEL : E ≤ Subgroup.closure (conjugacyWithin Y r))
    (hE4 : 4 ≤ Nat.card E) :
    let L := Subgroup.closure (conjugacyWithin Y r)
    let R := (CFSG.oddCore Y).map Y.subtype
    fusionStronglyEmbedded (H.subgroupOf L) ∧ conjugacyWithin Y r = conjugacyWithin L r ∧
      2 ≤ twoRank L ∧ ⁅R, L⁆ = ⊥ ∧ fusionIsBenderGroup (L ⧸ CFSG.oddCore L) := by
  intro L R
  have hrc : r ∈ conjugacyWithin H z := hQclass ▸ (⟨hrQ, hr1⟩ : r ∈ (Q : Set G) \ {1})
  obtain ⟨k, hk⟩ := hrc
  have hk' : rightConjugateElem z (k : G) = r := hk
  have h' := minimalLocalFailure_right_conjugate h k k.2
  rw [hk'] at h'
  obtain ⟨hM, hclass, hxor⟩ :=
    minimalLocalFailure_proper_local_hull_dichotomy h' hcomm hsmallerR1 hY hrY hYH
  have hQ2 : IsPGroup 2 Q := fun x => ⟨1, Subtype.ext (by simpa using hQ.2 x x.2)⟩
  have hE2 : IsPGroup 2 E := hQ2.to_le hEQ
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hEcard : Nat.card (E.subgroupOf L) = 2 ^ n := by
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hEelem : IsElemAbelian 2 (E.subgroupOf L) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · have hc := congrArg Subtype.val (hQ.1.is_comm.comm (⟨((a : L) : G), hEQ a.2⟩ : Q)
        ⟨((b : L) : G), hEQ b.2⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using hc
    · apply Subtype.ext
      simpa using hQ.2 _ (hEQ ha)
  have hrank : 2 ≤ twoRank L := hn2.trans
    (CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary L _ hEelem n hEcard)
  rcases hxor.or with hone | htwo
  · obtain ⟨hone1, -⟩ := hone
    have hone2 : twoRank L = 1 := hone1
    omega
  · obtain ⟨-, hRL, -, -, hbender, -⟩ := htwo
    exact ⟨hM, hclass, hrank, hRL, hbender⟩

theorem hull_point_involution_card {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {Q : Subgroup G} (hQ : IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {Y : Subgroup G}
    {r : G} (hrQ : r ∈ Q) (hr1 : r ≠ 1) (hrY : r ∈ Y)
    (hM : fusionStronglyEmbedded (H.subgroupOf (Subgroup.closure (conjugacyWithin Y r))))
    (hEL : Q ⊓ Y ≤ Subgroup.closure (conjugacyWithin Y r)) :
    Nat.card {x : Subgroup.closure (conjugacyWithin Y r) //
        x ∈ H.subgroupOf (Subgroup.closure (conjugacyWithin Y r)) ∧ IsInvolution x} =
      Nat.card (Q ⊓ Y : Subgroup G) - 1 := by
  let L := Subgroup.closure (conjugacyWithin Y r)
  have hLY : L ≤ Y := by
    apply (Subgroup.closure_le _).mpr
    rintro w ⟨k, rfl⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem k.2) hrY) k.2
  have hrL : r ∈ L := Subgroup.subset_closure ⟨1, by simp⟩
  let rL : L := ⟨r, hrL⟩
  have hrInv : IsInvolution rL :=
    ⟨fun h1 => hr1 (congrArg Subtype.val h1), Subtype.ext (by simpa using hQ.2 r hrQ)⟩
  have hnative := native_strong_embedding_of_order_conditions hM
  have hrD : r ∈ involutionPointClass z := point_subgroup_class h hQclass ⟨hrQ, hr1⟩
  have hQH : Q ≤ H := point_subgroup_le h.distinguished_mem hQclass
  rw [← card_diff_one]
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨((x : L) : G), ?_⟩
      invFun := fun w => ⟨⟨w, hEL w.2.1⟩, hQH w.2.1.1,
        ⟨fun h1 => w.2.2 (congrArg Subtype.val h1),
          Subtype.ext (by simpa using hQ.2 _ w.2.1.1)⟩⟩
      left_inv := fun x => rfl
      right_inv := fun w => rfl }
  obtain ⟨g, hg⟩ := CFSG.BenderSuzuki.IsStronglyEmbedded.involutions_conjugate hnative hrInv x.2.2
  have hxg : ((x : L) : G) = ((g : L) : G)⁻¹ * r * (g : L) := by
    rw [← hg]
    rfl
  have hxD : ((x : L) : G) ∈ involutionPointClass z := by
    rw [hxg]
    exact conj_mem_pointClass hrD _
  have hxH : ((x : L) : G) ∈ (H : Set G) := x.2.1
  have hxQ : ((x : L) : G) ∈ (Q : Set G) \ {1} := by
    rw [← class_inter_point h hQclass]
    exact ⟨hxD, hxH⟩
  exact ⟨⟨hxQ.1, hLY (x : L).2⟩, hxQ.2⟩

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
