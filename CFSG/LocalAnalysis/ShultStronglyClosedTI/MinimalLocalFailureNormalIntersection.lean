module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNormalIntersectionRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G] [Finite G]

theorem minimalLocalFailureNormalIntersectionSylowHullRank
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (C : Subgroup G) (hCB : C ≤ pairPointStabilizer H beta)
    (hC : Subgroup.closure ((pairPointStabilizer H beta : Set G) ∪ {t}) ≤
      Subgroup.normalizer (C : Set G))
    (p : ℕ) (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    (Q : Sylow p (C ⊓ triplePointStabilizer H z beta : Subgroup G))
    (hzQ : z ∈ Subgroup.normalizer
      (((Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
        (C ⊓ triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (hUne : ((Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
      (C ⊓ triplePointStabilizer H z beta).subtype : Subgroup G) ≠ ⊥)
    (hdeficient : ¬ ∃ R : Sylow p C,
      (R : Subgroup C).map C.subtype =
        (Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
          (C ⊓ triplePointStabilizer H z beta).subtype) :
    let U := (Q : Subgroup (C ⊓ triplePointStabilizer H z beta : Subgroup G)).map
      (C ⊓ triplePointStabilizer H z beta).subtype
    let Y := Subgroup.normalizer (U : Set G)
    Y ≠ ⊤ ∧ ¬ Y ≤ H ∧
      (∃ y : Y, pointRightCosetMul H (rightCosetMk H 1) y = beta) ∧
      2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin Y z)) ∧
      (∀ hzY : z ∈ Y,
        InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨z, hzY⟩ : Y) ∧
          ∃ (T : Sylow 2 Y) (hzT : (⟨z, hzY⟩ : Y) ∈ (T : Subgroup Y)),
            (⟨(⟨z, hzY⟩ : Y), hzT⟩ : (T : Subgroup Y)) ∈
              Subgroup.center (T : Subgroup Y)) ∧
      (∃ s : G, s ∈ conjugacyWithin (pairPointStabilizer H beta) t ∧ s ∈ Y ∧
        s ∈ rightPairFlipFiber H z beta ∧
        pointRightCosetMul H (rightCosetMk H 1) s = beta ∧
        pointRightCosetMul H beta s = rightCosetMk H 1) := by
  let E := triplePointStabilizer H z beta
  let U := (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype
  let Y := Subgroup.normalizer (U : Set G)
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hdoubly := (minimalLocalFailureSylowFixedPointsFromProperCommutingImages h hcomm).2.2.1
  obtain ⟨s, hsclass, hsY⟩ := local_involution_point_normalized_intersection_sylow_flips
    H z h.local_datum S hzS hzcenter hdoubly beta hbeta t ht C hC p hp Q
  have hsfiber : s ∈ rightPairFlipFiber H z beta := by
    rw [pair_flip_fiber_eq_stabilizer_class h.local_datum S hzS hzcenter hbeta ht]
    exact hsclass
  have hsbase : pointRightCosetMul H (rightCosetMk H 1) s = beta :=
    (pointRightCosetMul_eq_translate H _ _).trans hsfiber.2
  have hsreturn : pointRightCosetMul H beta s = rightCosetMk H 1 :=
    (pointRightCosetMul_eq_translate H _ _).trans
      (right_pair_flip_returns h.local_datum.distinguished_order hsfiber)
  obtain ⟨hsimple, hnonab⟩ := minimalLocalFailure_nonabelian_simple h
  let _ := hsimple
  have hYproper : Y ≠ ⊤ := prime_subgroup_normalizer_ne_top
    hnonab p hp U (Q.isPGroup'.map (C ⊓ E).subtype) hUne
  have hYescape : ¬ Y ≤ H := fun hYH => pair_flip_not_mem_point hbeta hsfiber (hYH hsY)
  have hBnormalizes : pairPointStabilizer H beta ≤ Subgroup.normalizer (C : Set G) := by
    intro b hb
    exact hC (Subgroup.subset_closure (Set.mem_union_left _ hb))
  have hrank := normalIntersection_deficient_sylow_hull_rank
    h hcomm beta hbeta C hCB hBnormalizes p hp hpm Q hzQ hUne hdeficient
  refine ⟨hYproper, hYescape, ⟨⟨s, hsY⟩, hsbase⟩, hrank, ?_,
    ⟨s, hsclass, hsY, hsfiber, hsbase, hsreturn⟩⟩
  intro hzY
  obtain ⟨hlocal, hcentral⟩ := involution_point_subgroup_inheritance
    h.local_datum Y hzY hYescape
  exact ⟨hlocal, hcentral ⟨S, hzS, hzcenter⟩⟩

end CFSG.ShultStronglyClosedTI
