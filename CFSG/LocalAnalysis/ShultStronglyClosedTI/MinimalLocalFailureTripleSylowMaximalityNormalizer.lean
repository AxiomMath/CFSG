module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleNormalizerRankTwo
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

theorem leastFailure_triple_normalizer_hull
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hUne : ((P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥) :
    let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let N := Subgroup.normalizer (U : Set G)
    let zN : N := ⟨z, hzP⟩
    let L := involutionPointHull zN
    let Delta := pointFixedSet H U
    Odd p ∧ N ≠ ⊤ ∧ L.Normal ∧
      fusionStronglyEmbedded ((H.subgroupOf N).subgroupOf L) ∧
      TwoRankAtLeastTwo L ∧
      (rightCosetMk H 1 ≠ beta ∧
        rightCosetMk H 1 ≠ pointRightCosetMul H beta z ∧
        beta ≠ pointRightCosetMul H beta z) ∧
      (rightCosetMk H 1 ∈ Delta ∧ beta ∈ Delta ∧
        pointRightCosetMul H beta z ∈ Delta) ∧
      (∀ a b : pointRightCosetSpace H, a ∈ Delta → b ∈ Delta →
        ∃ l : L, pointRightCosetMul H a (((l : N) : G)) = b) := by
  let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  let N := Subgroup.normalizer (U : Set G)
  let zN : N := ⟨z, hzP⟩
  let L := involutionPointHull zN
  obtain ⟨hmOdd, _hmOne, hdoubly, hSylows⟩ :=
    minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm
  have hpodd : Odd p := hmOdd.of_dvd_nat hpm
  have hambient : ∀ Q : Sylow p G, Nat.card (pointFixedSet H (Q : Subgroup G)) = 2 :=
    fun Q => (hSylows p hp hpm).1 Q |>.1
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨hdist, hpoints, _hcentral, _hNescape, _hNtwo, hlocal, hcentralSylow,
    _hcosets, hflips, hproper⟩ :=
    local_involution_point_triple_sylow_normalizer_double_transitivity
      H z h.local_datum S hzS hzcenter hdoubly beta hbeta p hp P hzP
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  have hNproper : N ≠ ⊤ := hproper hsimple hnonab hUne
  have hNcard : Nat.card N < Nat.card G := by
    simpa only [Subgroup.card_top] using
      Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNproper)
  have hstrong : fusionStronglyEmbedded ((H.subgroupOf N).subgroupOf L) :=
    h.smaller N hNcard (H.subgroupOf N) zN hlocal hcentralSylow
  have hLnormal : L.Normal := minimalLocalFailure_hull_normal zN
  have hLrankOriginal :=
    (local_involution_point_triple_sylow_normalizer_involution_hull_rank_two
      H z h.local_datum S hzS hzcenter hdoubly beta hbeta p hp hpodd
      hambient P hzP).2.2.2.2
  have hLrank : 2 ≤ CFSG.Open.twoRank L := by
    rw [internal_involution_hull_rank_eq_original_class_closure N z hzP] at hLrankOriginal
    exact hLrankOriginal
  refine ⟨hpodd, hNproper, hLnormal, hstrong,
    native_rank_two_of_two_le_twoRank hLrank, hdist, hpoints, ?_⟩
  intro a b ha hb
  by_cases hab : a = b
  · subst b
    exact ⟨1, pointRightCosetMul_one H a⟩
  · obtain ⟨n, hn, _hnback⟩ := hflips a b ha hb hab
    let t : N := rightConjugateElem zN n
    have ht : t ∈ L := Subgroup.subset_closure ⟨n, rfl⟩
    exact ⟨⟨t, ht⟩, hn⟩

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
