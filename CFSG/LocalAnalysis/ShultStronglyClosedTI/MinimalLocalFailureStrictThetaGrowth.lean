module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthConstruction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthGeneration
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthStrictness
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaCoreContainment

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.StrictThetaGrowth

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailure_strict_theta_core_growth
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    let B := pairPointStabilizer H beta
    let E := triplePointStabilizer H z beta
    let J := pairOddCore H beta
    let V := (CFSG.oddCore E).map E.subtype
    ∀ P : Sylow p V,
      let X := (P : Subgroup V).map V.subtype
      rightConjugate X z = X → ¬ X ≤ Subgroup.centralizer ({z} : Set G) →
      ∀ t : G, t ∈ rightPairFlipFiber H z beta →
        t ∈ Subgroup.normalizer (X : Set G) →
        2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
          (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)) →
        minimalLocalFailurePairConfinementTheta p E <
          minimalLocalFailurePairConfinementTheta p B ∧
        ∃ Q : Sylow p J, ∃ u : G,
          u ∈ rightPairFlipFiber H z beta ∧
          rightConjugate ((Q : Subgroup J).map J.subtype) u =
            (Q : Subgroup J).map J.subtype ∧
          rightConjugate
            ((orderZJ ((Q : Subgroup J).map J.subtype)).map
              ((Q : Subgroup J).map J.subtype).subtype) z =
            (orderZJ ((Q : Subgroup J).map J.subtype)).map
              ((Q : Subgroup J).map J.subtype).subtype ∧
          (orderZJ ((Q : Subgroup J).map J.subtype)).map
            ((Q : Subgroup J).map J.subtype).subtype ≠ ⊥ := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let J := pairOddCore H beta
  let V := (CFSG.oddCore E).map E.subtype
  dsimp only
  intro P
  let X := (P : Subgroup V).map V.subtype
  intro hXz hnoncentral t ht htX hrank
  obtain ⟨_hV, _hsaturation, _hcapture, hcontain⟩ :=
    ThetaCoreContainment.minimalLocalFailure_theta_core_containment h hFR beta hbeta
      p hp hpodd P hXz hnoncentral t ht htX hrank
  have hadm := original_sylow_admissible h beta hbeta p hp P hXz hnoncentral t ht htX hrank
  obtain ⟨Q, u, hu, huQ, hQne, hzZQ, hZQne⟩ := exists_full_sylow_and_normalized_orderZJ
    h hcomm beta hbeta p hp hpodd ⟨X, X, t, hadm⟩
  have hXE : X ≤ E := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hgen := generation_of_noncentral_triple_subgroup h hcomm hbeta hXE hnoncentral hu
  have hstrict := theta_strict_of_full_sylow h beta hbeta p hp hpodd Q hQne u hu huQ
    hzZQ hgen hcontain
  exact ⟨hstrict, Q, u, hu, rightConjugate_eq_self_of_mem_normalizer huQ,
    rightConjugate_eq_self_of_mem_normalizer hzZQ, hZQne⟩

end CFSG.ShultStronglyClosedTI
