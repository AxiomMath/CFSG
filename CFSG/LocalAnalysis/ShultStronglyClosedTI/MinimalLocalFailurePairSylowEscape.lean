module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairSylowMinimum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyGeneration
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementContradiction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowth

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem pairSylow_opposite_theta_escape
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    {beta : rightCosetSpace H} (hbeta : beta ∈ pairSylowFullTriplePairs H z p)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hcomparison :
      Nat.card (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)) ≤
        Nat.card (minimalLocalFailurePairConfinementTheta p
          (oppositePairStabilizer H z beta))) :
    ¬ minimalLocalFailurePairConfinementTheta p (oppositePairStabilizer H z beta) ≤ H := by
  obtain ⟨hsimple, hnonabelian⟩ := minimalLocalFailure_nonabelian_simple h
  let : IsSimpleGroup G := hsimple
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hbasegen := fullPointPairGeneration_base h.local_datum hgen beta hbeta.1 t ht
  have hgrowth := (local_involution_point_generated_pair_strict_core_growth
    hnonabelian h.local_datum S hzS hzcenter hbeta.1 ht hbasegen p hp hodd hbeta.2).1
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let F := oppositePairStabilizer H z beta
  change Nat.card (minimalLocalFailurePairConfinementTheta p B) ≤
    Nat.card (minimalLocalFailurePairConfinementTheta p F) at hcomparison
  have hEF : E ≤ F := triple_stabilizer_le_opposite_pair H z beta
  have hlt : Nat.card (minimalLocalFailurePairConfinementTheta p E) <
      Nat.card (minimalLocalFailurePairConfinementTheta p B) :=
    pairConfinement_theta_strict_card p E B hgrowth
  intro hconfined
  have hthetaE : minimalLocalFailurePairConfinementTheta p F ≤ E := by
    intro x hx
    have hxF := pairConfinement_theta_le p F hx
    refine ⟨⟨?_, hxF.1⟩, hxF.2⟩
    rw [rightCosetStabilizer_base]
    exact hconfined hx
  have hcore := pairConfinement_theta_restrict p hp F E hEF hthetaE
  have hcard : Nat.card (minimalLocalFailurePairConfinementTheta p F) ≤
      Nat.card (minimalLocalFailurePairConfinementTheta p E) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hcore) (Subgroup.inclusion_injective hcore)
  omega

theorem pairSylow_bad_sylow_inverted_centralizer_escape
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hbad : ∃ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) ≠ 2) :
    ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ H ∧
      z ∈ Subgroup.normalizer (P : Set G) ∧
      Nat.card (conjugacyWithin P z) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p ∧
      ¬ Subgroup.centralizer (minimalLocalFailureInvertedSet P z) ≤ H := by
  obtain ⟨beta, hbeta, P, hP, hPH, hPF, hzP, hmotion,
    t, ht, _, _, hcomparison⟩ := pairSylow_minimum_pair_opposite_transport h p hp hodd hbad
  let F := oppositePairStabilizer H z beta
  let Y := minimalLocalFailurePairConfinementTheta p F
  have hescape : ¬ Y ≤ H := pairSylow_opposite_theta_escape h hgen p hp hodd hbeta ht
    hcomparison
  have hPY : P ≤ Subgroup.normalizer (Y : Set G) :=
    hPF.trans (Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p F))
  have hzY : z ∈ Subgroup.normalizer (Y : Set G) :=
    pairConfinement_theta_normalizer p F (opposite_pair_normalized_by_distinguished
      h.local_datum beta)
  obtain ⟨hYodd, hYcop⟩ := pairConfinement_theta_order p hp F
  obtain ⟨hPodd, hcop⟩ := pairConfinement_p_actor_coprime p hp hodd P Y hP hYodd hYcop
  have hcentralEscape := pairConfinement_odd_inverted_centralizer_escape H P Y z
    h.local_datum.distinguished_order (point_centralizer_le h.local_datum)
    hPH hPodd hzP hPY hzY hcop hescape
  refine ⟨P, hP, hPH, hzP, hmotion, ?_⟩
  intro hcentral
  exact hcentralEscape (inf_le_right.trans hcentral)

end CFSG.ShultStronglyClosedTI
