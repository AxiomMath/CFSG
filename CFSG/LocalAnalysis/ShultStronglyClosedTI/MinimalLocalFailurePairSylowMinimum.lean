module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairSylowSelection
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeCoreConjugation

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.SignalizerFunctor.Helpers
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def pairSylowFullTriplePairs (H : Subgroup G) (z : G) (p : ℕ) :
    Set (rightCosetSpace H) :=
  {beta | beta ≠ rightCosetMk H 1 ∧
    ∃ Q : Sylow p (pairPointStabilizer H beta),
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta}

variable [Finite G]

theorem pairSylow_theta_rightConjugate (p : ℕ) (D : Subgroup G) (n : G) :
    rightConjugate (minimalLocalFailurePairConfinementTheta p D) n =
      minimalLocalFailurePairConfinementTheta p (rightConjugate D n) := by
  unfold minimalLocalFailurePairConfinementTheta
  rw [← generatedPairGrowth_literal_core_eq_canonical,
    ← generatedPairGrowth_literal_core_eq_canonical]
  exact embedded_prime_core_conjugate (generatedPairGrowthPrimes p) n⁻¹ D

theorem pairSylow_theta_rightConjugate_card (p : ℕ) (D : Subgroup G) (n : G) :
    Nat.card (minimalLocalFailurePairConfinementTheta p (rightConjugate D n)) =
      Nat.card (minimalLocalFailurePairConfinementTheta p D) := by
  rw [← pairSylow_theta_rightConjugate]
  change Nat.card ((minimalLocalFailurePairConfinementTheta p D).map
    (MulAut.conj n⁻¹).toMonoidHom) = _
  exact Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective

theorem pairSylow_bad_sylow_minimum_pair
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hbad : ∃ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) ≠ 2) :
    ∃ beta ∈ pairSylowFullTriplePairs H z p,
      ∀ delta ∈ pairSylowFullTriplePairs H z p,
        Nat.card (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)) ≤
          Nat.card (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H delta)) := by
  have hfamily : (pairSylowFullTriplePairs H z p).Nonempty :=
    pairSylow_bad_sylow_full_pair_family h p hp hodd hbad
  exact Set.exists_min_image _ _ (Set.toFinite _) hfamily

theorem pairSylow_minimum_pair_opposite_transport
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hbad : ∃ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) ≠ 2) :
    ∃ beta ∈ pairSylowFullTriplePairs H z p,
      ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ H ∧
        P ≤ oppositePairStabilizer H z beta ∧
        z ∈ Subgroup.normalizer (P : Set G) ∧
        Nat.card (conjugacyWithin P z) =
          p ^ (Nat.card (conjugacyWithin H z)).factorization p ∧
        ∃ t ∈ rightPairFlipFiber H z beta,
          rightCosetTranslate H beta t = rightCosetMk H 1 ∧
          t ∈ Subgroup.normalizer (P : Set G) ∧
          Nat.card (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)) ≤
            Nat.card (minimalLocalFailurePairConfinementTheta p
              (oppositePairStabilizer H z beta)) := by
  obtain ⟨beta, hbeta, hmin⟩ := pairSylow_bad_sylow_minimum_pair h p hp hodd hbad
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have htransport := local_involution_point_full_pair_sylow_three_point_transport
    h.local_datum S hzS hzcenter hbeta.1 p hp hbeta.2
  let E := triplePointStabilizer H z beta
  let V := (CFSG.oddCore E).map E.subtype
  obtain ⟨P₀, hzP⟩ := htransport.2.2.2.2.2.1
  let P := (P₀ : Subgroup V).map V.subtype
  have hPE : P ≤ E := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hPH : P ≤ H := hPE.trans (inf_le_left.trans (pairPointStabilizer_le_point H beta))
  have hPF : P ≤ oppositePairStabilizer H z beta :=
    hPE.trans (triple_stabilizer_le_opposite_pair H z beta)
  obtain ⟨_, _, hmotion, t, ht, htreturn, htP, hdelta, hpair, htriple⟩ :=
    htransport.2.2.2.2.2.2 P₀ hzP
  let delta := rightCosetTranslate H (rightCosetTranslate H beta z) t
  have hdeltafamily : delta ∈ pairSylowFullTriplePairs H z p := by
    refine ⟨hdelta, ?_⟩
    rw [hpair] at htriple
    exact htriple
  have hcomparison := hmin delta hdeltafamily
  rw [← hpair, pairSylow_theta_rightConjugate_card] at hcomparison
  exact ⟨beta, hbeta, P, P₀.isPGroup'.map V.subtype, hPH, hPF,
    hzP, hmotion, t, ht, htreturn, htP, hcomparison⟩

end CFSG.ShultStronglyClosedTI
