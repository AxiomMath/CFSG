module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaHallGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullThetaAction
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaCoreContainment

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ShultStronglyClosedTI.ThetaHall

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailure_theta_core_Hall_subgroup
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    let B := pairPointStabilizer H beta
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    let C := minimalLocalFailurePairConfinementTheta p B
    let D := minimalLocalFailurePairConfinementTheta p E
    ∀ P : Sylow p V,
      let X := (P : Subgroup V).map V.subtype
      rightConjugate X z = X → ¬ X ≤ Subgroup.centralizer ({z} : Set G) →
      ∀ t : G, t ∈ rightPairFlipFiber H z beta →
        t ∈ Subgroup.normalizer (X : Set G) →
        2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
          (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)) →
        D ≤ C ∧
          CFSG.IsHallSubgroup {r : Nat.Primes | r.val ∣ Nat.card D} (D.subgroupOf C) ∧
          Nat.Coprime (Nat.card D) (D.relIndex C) := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let J := pairOddCore H beta
  let V := (CFSG.oddCore E).map E.subtype
  let C := minimalLocalFailurePairConfinementTheta p B
  let D := minimalLocalFailurePairConfinementTheta p E
  dsimp only
  intro P
  let X := (P : Subgroup V).map V.subtype
  intro hXz hnoncentral t ht htX hrank
  obtain ⟨hV, _hsaturation, _hcomplement, hcontain⟩ :=
    ThetaCoreContainment.minimalLocalFailure_theta_core_containment h hFR beta hbeta
      p hp hpodd P hXz hnoncentral t ht htX hrank
  have hXE : X ≤ E := (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  have hVeq : V = J ⊓ E := hV
  have hVJ : V ≤ J := by rw [hVeq]; exact inf_le_left
  have hXJ : X ≤ J := (Subgroup.map_subtype_le _).trans hVJ
  have hXp : IsPGroup p X := P.isPGroup'.map V.subtype
  have hintersection : C ⊓ E = D :=
    properHull_theta_inf_subgroup_eq p hp B E inf_le_left hcontain
  have hcoprime : Nat.Coprime (Nat.card D) (D.relIndex C) := by
    by_contra hn
    obtain ⟨q, hq, hqD, hqindex⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hjoint : ∃ Q : Sylow q (C ⊓ E : Subgroup G),
        let U := (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype
        U ≠ ⊥ ∧ X ≤ Subgroup.normalizer (U : Set G) ∧
          z ∈ Subgroup.normalizer (U : Set G) := by
      rw [hintersection]
      obtain ⟨Q, hQne, _hQp, _hQle, hXQ, hzQ⟩ :=
        properHull_theta_nontrivial_joint_sylow p q hp hq E X z hXp
          h.local_datum.distinguished_order
          (mem_normalizer_of_rightConjugate_eq_self hXz)
          (hXE.trans Subgroup.le_normalizer)
          (triple_stabilizer_normalized_by_distinguished h.local_datum beta) hqD
      exact ⟨Q, hQne, hXQ, hzQ⟩
    obtain ⟨Q, hQne, hXQ, hzQ⟩ := hjoint
    have hcapture := original_deficient_theta_sylow_capture h hcomm beta hbeta t ht
      p q hp hpodd hq hcontain hqindex Q hzQ hQne X hXJ hXp hXz hnoncentral hXQ
    have hindex : q ∣ (C ⊓ E).relIndex C := by
      rw [hintersection]
      exact hqindex
    exact sylow_deficient_of_relIndex_prime q hq C E hindex Q
      (sylow_of_theta_normalizer_capture p q hp hq B E Q hcapture)
  have hcard : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcontain).toEquiv
  refine ⟨hcontain, ?_, hcoprime⟩
  refine CFSG.isHallSubgroup_of _ _ ?_ ?_
  · intro r hr
    change r.val ∣ Nat.card D
    rwa [hcard] at hr
  · intro r hr hi
    change r.val ∣ Nat.card D at hr
    change r.val ∣ D.relIndex C at hi
    exact r.property.ne_one (Nat.eq_one_of_dvd_coprimes hcoprime hr hi)

end CFSG.ShultStronglyClosedTI
