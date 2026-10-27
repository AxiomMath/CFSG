module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSimple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaNormalizerLift
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementTheta
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

universe u

variable {G : Type u} [Group G]

theorem normal_of_pair_generation
    (z v : G) (J C : Subgroup G)
    (hgen : (Subgroup.zpowers z ⊔ Subgroup.zpowers v) ⊔ J = ⊤)
    (hz : z ∈ Subgroup.normalizer (C : Set G))
    (hv : v ∈ Subgroup.normalizer (C : Set G))
    (hJ : J ≤ Subgroup.normalizer (C : Set G)) : C.Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [← hgen]
  exact sup_le (sup_le (Subgroup.zpowers_le.mpr hz)
    (Subgroup.zpowers_le.mpr hv)) hJ

variable [Finite G]

theorem theta_strict_of_full_sylow
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (Q : Sylow p (pairOddCore H beta))
    (hQne : (Q : Subgroup (pairOddCore H beta)) ≠ ⊥)
    (v : G) (hv : v ∈ rightPairFlipFiber H z beta)
    (hvQ : v ∈ Subgroup.normalizer
      ((Q : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype : Set G))
    (hzZQ : z ∈ Subgroup.normalizer
      ((orderZJ ((Q : Subgroup (pairOddCore H beta)).map
        (pairOddCore H beta).subtype)).map
          ((Q : Subgroup (pairOddCore H beta)).map (pairOddCore H beta).subtype).subtype :
            Set G))
    (hgen : (Subgroup.zpowers z ⊔ Subgroup.zpowers v) ⊔ pairOddCore H beta = ⊤)
    (hcontain : minimalLocalFailurePairConfinementTheta p
      (triplePointStabilizer H z beta) ≤
        minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)) :
    minimalLocalFailurePairConfinementTheta p (triplePointStabilizer H z beta) <
      minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsSimpleGroup G := (minimalLocalFailure_nonabelian_simple h).1
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let J := pairOddCore H beta
  let AQ := (Q : Subgroup J).map J.subtype
  let R := (orderZJ AQ).map AQ.subtype
  have hRQ : R ≤ AQ := Subgroup.map_subtype_le _
  have hRJ : R ≤ J := hRQ.trans (Subgroup.map_subtype_le _)
  have hRchar : (orderZJ AQ).Characteristic := primeComplementGrowth_order_zj_characteristic
  have hvR : v ∈ Subgroup.normalizer (R : Set G) :=
    generatedPairGrowth_normalizer_le_characteristic_image AQ (orderZJ AQ) hRchar hvQ
  have hAQne : AQ ≠ ⊥ := by
    intro hbot
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hbot)
  let : Nontrivial AQ := (Subgroup.nontrivial_iff_ne_bot AQ).mpr hAQne
  have hRne : R ≠ ⊥ := by
    intro hbot
    exact primeComplementGrowth_order_zj_ne_bot p (Q.isPGroup'.map J.subtype)
      ((Subgroup.map_eq_bot_iff_of_injective _ AQ.subtype_injective).mp hbot)
  have hthetaB : minimalLocalFailurePairConfinementTheta p B =
      (CFSG.pPrimeCore p J).map J.subtype :=
    generatedPairGrowth_ambient_canonical_core_eq B hp
  have hthetaBne : minimalLocalFailurePairConfinementTheta p B ≠ ⊥ := by
    intro hbot
    have hcore : CFSG.pPrimeCore p J = ⊥ := by
      rw [hthetaB] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hbot
    have hchar := primeComplementGrowth_odd_product_characteristic p hpodd
      (pairOddCore_odd H beta) Q
    rw [hcore, bot_sup_eq] at hchar
    have hcop : Nat.Coprime p (Nat.card J.subtype.ker) := by
      rw [MonoidHom.ker_eq_bot _ J.subtype_injective, Subgroup.card_bot]
      exact Nat.coprime_one_right p
    have hmap : (((orderZJ (Q : Subgroup J)).map (Q : Subgroup J).subtype).map
        J.subtype) = R :=
      LocalTheta.orderZJ_image_of_coprime_kernel hp J.subtype hcop Q Q.isPGroup'
    have hJR : J ≤ Subgroup.normalizer (R : Set G) := by
      rw [← hmap]
      exact Subgroup.le_normalizer.trans
        (generatedPairGrowth_normalizer_le_characteristic_image J _ hchar)
    let : R.Normal := normal_of_pair_generation z v J R hgen hzZQ hvR hJR
    exact hRne (generatedPairGrowth_normal_subgroup_in_pair_odd_core_eq_bot
      h.local_datum beta R hRJ)
  have hne : minimalLocalFailurePairConfinementTheta p E ≠
      minimalLocalFailurePairConfinementTheta p B := by
    intro heq
    let C := minimalLocalFailurePairConfinementTheta p B
    have hzC : z ∈ Subgroup.normalizer (C : Set G) := by
      dsimp only [C]
      rw [← heq]
      exact pairConfinement_theta_normalizer p E
        (triple_stabilizer_normalized_by_distinguished h.local_datum beta)
    have hvC : v ∈ Subgroup.normalizer (C : Set G) := by
      have hvJ := generatedPairGrowth_flip_normalizes_pair_odd_core h.local_datum hbeta hv
      dsimp only [C]
      rw [hthetaB]
      exact generatedPairGrowth_normalizer_le_characteristic_image
        J (CFSG.pPrimeCore p J) inferInstance hvJ
    have hJC : J ≤ Subgroup.normalizer (C : Set G) := by
      dsimp only [C]
      rw [hthetaB]
      exact Subgroup.le_normalizer.trans
        (generatedPairGrowth_normalizer_le_characteristic_image J (CFSG.pPrimeCore p J)
          inferInstance)
    have hCJ : C ≤ J := by
      dsimp only [C]
      rw [hthetaB]
      exact Subgroup.map_subtype_le _
    let : C.Normal := normal_of_pair_generation z v J C hgen hzC hvC hJC
    exact hthetaBne (generatedPairGrowth_normal_subgroup_in_pair_odd_core_eq_bot
      h.local_datum beta C hCJ)
  exact lt_of_le_of_ne hcontain hne

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
