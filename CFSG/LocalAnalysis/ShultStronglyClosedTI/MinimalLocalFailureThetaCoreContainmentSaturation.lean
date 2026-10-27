module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureThetaCoreContainmentGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralizerSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ThetaCoreContainment

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_triple_odd_sylow_centralizer_saturated
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hFR : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Sylow p ((CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype))
    (hPz : rightConjugate ((P : Subgroup ((CFSG.oddCore
      (triplePointStabilizer H z beta)).map (triplePointStabilizer H z beta).subtype)).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype) z =
      (P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype)
    (hnoncentral : ¬ (P : Subgroup ((CFSG.oddCore
      (triplePointStabilizer H z beta)).map (triplePointStabilizer H z beta).subtype)).map
        ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype).subtype ≤
            Subgroup.centralizer ({z} : Set G))
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (htP : t ∈ Subgroup.normalizer
      (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype)).map
          ((CFSG.oddCore (triplePointStabilizer H z beta)).map
            (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G))
    (hrank : 2 ≤ CFSG.Open.pRank 2 (Subgroup.closure
      (conjugacyWithin (Subgroup.normalizer
        (((P : Subgroup ((CFSG.oddCore (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype)).map
            ((CFSG.oddCore (triplePointStabilizer H z beta)).map
              (triplePointStabilizer H z beta).subtype).subtype : Subgroup G) : Set G)) z))) :
    let V := (CFSG.oddCore (triplePointStabilizer H z beta)).map
      (triplePointStabilizer H z beta).subtype
    let X := (P : Subgroup V).map V.subtype
    ∀ x : G, x ∈ pairOddCore H beta → x ∈ Subgroup.centralizer (X : Set G) →
      CFSG.IsPElement p x → x ∈ X := by
  let : Fact p.Prime := ⟨hp⟩
  let E := triplePointStabilizer H z beta
  let J := pairOddCore H beta
  let V := (CFSG.oddCore E).map E.subtype
  let X := (P : Subgroup V).map V.subtype
  let B := pairPointStabilizer H beta
  have hXV : X ≤ V := Subgroup.map_subtype_le _
  have hVE : V ≤ E := Subgroup.map_subtype_le _
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hV : V = J ⊓ E := triple_odd_core_eq_pair_intersection
    h.local_datum S hzS hzcenter beta hbeta
  have hVJ : V ≤ J := by rw [hV]; exact inf_le_left
  have hJB : J ≤ B := Subgroup.map_subtype_le _
  have hXB : X ≤ B := hXV.trans (hVJ.trans hJB)
  have hXH : X ≤ H := hXB.trans (pairPointStabilizer_le_point H beta)
  have hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H := by
    intro hNH
    exact pair_flip_not_mem_point hbeta ht (hNH htP)
  have hbetaorbit : beta ∈ numeratorRightOrbit H
      (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1) := by
    refine ⟨t, htP, ?_⟩
    exact (pointRightCosetMul_eq_translate H _ _).trans ht.2
  change ∀ x : G, x ∈ J → x ∈ Subgroup.centralizer (X : Set G) →
    CFSG.IsPElement p x → x ∈ X
  intro x hxJ hxcent hxp
  let C := B ⊓ Subgroup.centralizer (X : Set G)
  have hxC : x ∈ C := ⟨hJB hxJ, hxcent⟩
  have hzp : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨n, hn⟩ := hxp
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hzC : Subgroup.zpowers x ≤ C := Subgroup.zpowers_le.mpr hxC
  have hzCp : IsPGroup p ((Subgroup.zpowers x).subgroupOf C) :=
    hzp.of_injective (Subgroup.subgroupOfEquivOfLe hzC).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hzC).injective
  obtain ⟨Q, hZQ⟩ := hzCp.exists_le_sylow
  let QG := (Q : Subgroup C).map C.subtype
  have hxQG : x ∈ QG := Subgroup.mem_map_of_mem C.subtype
    (hZQ (show (⟨x, hxC⟩ : C) ∈ (Subgroup.zpowers x).subgroupOf C from
      Subgroup.mem_zpowers x))
  obtain ⟨s, hsclass, _hsX, _hsQ, hsjoin⟩ :=
    minimalLocalFailure_centralizer_sylow_involution_normalizer
      h hFR X hXH hPz hnoncentral hescape hrank ⟨beta, hbetaorbit⟩ hbeta p hp hpodd Q
  rw [original_pair_class_eq h.local_datum S hzS hzcenter beta hbeta t ht] at hsclass
  obtain ⟨b, hb⟩ := hsclass
  let U := X ⊔ Subgroup.zpowers x
  have hXp : IsPGroup p X := P.isPGroup'.map V.subtype
  have hUp : IsPGroup p U := hXp.to_sup_of_normal_left' hzp
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (X : Set G) hxcent))
  have hWjoin : U ≤ X ⊔ QG :=
    sup_le le_sup_left ((Subgroup.zpowers_le.mpr hxQG).trans le_sup_right)
  have hjoinB : X ⊔ QG ≤ B := sup_le hXB
    ((Subgroup.map_subtype_le _).trans inf_le_left)
  have hjoinEs : X ⊔ QG ≤ triplePointStabilizer H s beta :=
    invariant_pair_subgroup_le_triple hjoinB hsjoin
  have hUJ : U ≤ J := sup_le (hXV.trans hVJ) (Subgroup.zpowers_le.mpr hxJ)
  have hUVb : U ≤ rightConjugate V b := by
    rw [pair_element_transports_triple_odd_core h.local_datum S hzS hzcenter beta hbeta
      b b.property]
    change U ≤ J ⊓ triplePointStabilizer H (b.val⁻¹ * z * b.val) beta
    rw [hb]
    exact le_inf hUJ (hWjoin.trans hjoinEs)
  have hcardVb : Nat.card (rightConjugate V b) = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj b.val⁻¹).injective
  have hXcard : Nat.card X = p ^ (Nat.card V).factorization p := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, P.card_eq_multiplicity]
  have hUcard : Nat.card U ≤ Nat.card X := by
    have hbound := p_subgroup_card_le_prime_part p hp (rightConjugate V b) U hUVb hUp
    rw [hcardVb, ← hXcard] at hbound
    exact hbound
  have hXU : X = U := Subgroup.eq_of_le_of_card_ge le_sup_left hUcard
  rw [hXU]
  exact (show Subgroup.zpowers x ≤ U from le_sup_right) (Subgroup.mem_zpowers x)

end CFSG.ShultStronglyClosedTI.ThetaCoreContainment
