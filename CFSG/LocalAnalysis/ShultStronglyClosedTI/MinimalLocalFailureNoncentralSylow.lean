module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowNormalizer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem minimalLocalFailureNoncentralOddSylowNormalizer
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hnoncentral : triplePointStabilizer H z beta ≠
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    V = E ⊓ pairOddCore H beta ∧
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (conjugacyWithin H z) ∧
      ∃ P : Sylow p V,
        let U := (P : Subgroup V).map V.subtype
        U ≠ ⊥ ∧ ¬ U ≤ Subgroup.centralizer ({z} : Set G) ∧
        ∃ t : G, t ∈ rightPairFlipFiber H z beta ∧
          z ∈ Subgroup.normalizer (U : Set G) ∧
          t ∈ Subgroup.normalizer (U : Set G) ∧
          Subgroup.normalizer (U : Set G) ≠ ⊤ ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ H ∧
          2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
            (conjugacyWithin (Subgroup.normalizer (U : Set G)) z)) ∧
          (∀ hzM : z ∈ Subgroup.normalizer (U : Set G),
            InvolutionPointLocalEmbedding
              (H.subgroupOf (Subgroup.normalizer (U : Set G)))
              (⟨z, hzM⟩ : Subgroup.normalizer (U : Set G)) ∧
            ∃ (T : Sylow 2 (Subgroup.normalizer (U : Set G)))
              (hzT : (⟨z, hzM⟩ : Subgroup.normalizer (U : Set G)) ∈
                (T : Subgroup (Subgroup.normalizer (U : Set G)))),
              (⟨(⟨z, hzM⟩ : Subgroup.normalizer (U : Set G)), hzT⟩ :
                (T : Subgroup (Subgroup.normalizer (U : Set G)))) ∈
                  Subgroup.center (T : Subgroup (Subgroup.normalizer (U : Set G)))) ∧
          (∀ A : Sylow p (Subgroup.normalizer (U : Set G) ⊓ pairPointStabilizer H beta : Subgroup G),
            U ≤ (A : Subgroup
              (Subgroup.normalizer (U : Set G) ⊓ pairPointStabilizer H beta : Subgroup G)).map
                (Subgroup.normalizer (U : Set G) ⊓ pairPointStabilizer H beta).subtype →
            ¬ (A : Subgroup
              (Subgroup.normalizer (U : Set G) ⊓ pairPointStabilizer H beta : Subgroup G)).map
                (Subgroup.normalizer (U : Set G) ⊓ pairPointStabilizer H beta).subtype ≤
                  Subgroup.centralizer ({z} : Set G)) := by
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  obtain ⟨hV, p, hp, hpodd, hpm, P, hUne, hUnoncentral, t, htfiber, hzU, htU,
    hMproper, hMescape, hlocal, hnoncentralOvergroups⟩ :=
    noncentralSylow_selected_proper_normalizer h beta hbeta hnoncentral
  have hrank := noncentralSylow_odd_core_normalizer_hull_rank
    h hcomm beta hbeta p hp hpm P hzU hUne
  refine ⟨?_, p, hp, hpodd, hpm, P, hUne, hUnoncentral, t, htfiber, hzU, htU,
    hMproper, hMescape, hrank, hlocal, ?_⟩
  · exact hV.trans (inf_comm _ _)
  · intro A hUA
    exact hnoncentralOvergroups _ hUA

end CFSG.ShultStronglyClosedTI
