module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaNormalization
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary85
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma101
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma106
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102ExponentData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowExtension
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowMoving
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowNormalizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded
public import Certificates.Certificate43

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.OrderReductions.PrimePart
open CFSG.ShultStronglyClosedTI.LocalTheta
open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailure_local_theta_and_ZJ_normalizer
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hA0 : ∃ A0 : Subgroup G,
      A0 ≤ Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta.val ∧
      IsPGroup p A0 ∧ rightConjugate A0 z = A0 ∧
      ⁅A0, Subgroup.zpowers z⁆ ≠ ⊥) :
    let Y := Subgroup.normalizer (X : Set G)
    let B := pairPointStabilizer H beta.val
    let E := triplePointStabilizer H z beta.val
    let J := pairOddCore H beta.val
    let D := Y ⊓ B
    let T := Y ⊓ J
    let Theta := minimalLocalFailurePairConfinementTheta p D
    let U := T ⊔ Theta
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    let W := (CFSG.pPrimeCore p K).map K.subtype
    Theta ≤ E ∧
      Theta = (CFSG.pPrimeCore p ((CFSG.oddCore D).map D.subtype)).map
        ((CFSG.oddCore D).map D.subtype).subtype ∧
      U ≤ D ∧ (U.subgroupOf D).Normal ∧ Odd (Nat.card U) ∧
      primePart p (Nat.card U) = primePart p (Nat.card T) ∧
      I ≤ H ⊓ Y ∧ (I.subgroupOf (H ⊓ Y)).Normal ∧ z ∈ I ∧
      I = Subgroup.closure (conjugacyWithin T z) ∧
      K ≤ H ⊓ Y ∧ D ≤ Subgroup.normalizer (K : Set G) ∧
      Group.IsSolvable K ∧ 2 ≤ CFSG.Open.pRank 2 K ∧
      (∀ S : Sylow 2 K, IsElementaryAbelian 2 (S : Subgroup K)) ∧
      {v : G | v ∈ K ∧ IsInvolution v} = conjugacyWithin T z ∧
      (∃ n : ℕ, U.relIndex K = 2 ^ n) ∧
      Odd (Nat.card W) ∧ Nat.Coprime p (Nat.card W) ∧
      (W.subgroupOf K).Normal ∧ Theta ≤ W ∧ W ≤ E ⊓ U ∧
      (U : Set G) = (T : Set G) * (Theta : Set G) ∧
      (K : Set G) = (I : Set G) * (U : Set G) ∧
      K = Subgroup.zpowers z ⊔ U ∧
      ∀ Q : Sylow p T,
        let QG := (Q : Subgroup T).map T.subtype
        let ZJ := (orderZJ QG).map QG.subtype
        theorem4bIsSylowSubgroupOf p QG K ∧
        (K : Set G) = (W : Set G) *
          (K ⊓ Subgroup.normalizer (ZJ : Set G) : Set G) ∧
        (conjugacyWithin E z ∩ (Subgroup.normalizer (ZJ : Set G) : Set G)).Nonempty ∧
        ∃ w ∈ W,
          IsInvolution (rightConjugateElem z w) ∧
          rightConjugateElem z w ∈ conjugacyWithin E z ∧
          rightConjugateElem z w ∈ Subgroup.normalizer (ZJ : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let B := pairPointStabilizer H beta.val
  let E := triplePointStabilizer H z beta.val
  let J := pairOddCore H beta.val
  let D := Y ⊓ B
  let T := Y ⊓ J
  let Theta := minimalLocalFailurePairConfinementTheta p D
  let U := T ⊔ Theta
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  let W := (CFSG.pPrimeCore p K).map K.subtype
  obtain ⟨A0, hA0T, hA0p, hA0z, hA0comm⟩ := hA0
  have hnoncentral : ¬ A0 ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hcent
    have hzC : z ∈ Subgroup.centralizer (A0 : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mp (hcent ha)
    have hzpowC : Subgroup.zpowers z ≤ Subgroup.centralizer (A0 : Set G) :=
      Subgroup.zpowers_le.mpr hzC
    exact hA0comm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mpr hzpowC))
  obtain ⟨S2, hzS2, hzcenter⟩ := h.central_sylow
  obtain ⟨_hDpoint, _hTD, _hTnormal, hUD, hUnormal, hUodd, hpart, _hSylowU,
    hIpoint, hInormal, hzI, hKpoint, hKnorm, _hIKnormal, hgen, hUprod, hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S2 hzS2 hzcenter Y hzY hescape
      beta hbeta hp
  obtain ⟨hsol, hfour, htwo, hclass, _himage⟩ :=
    local_theta_actual_structure h hcomm X hXH hXne hXz hescape hrank beta hbeta hp
  obtain ⟨_hIelem, _hIRU, hindex, _hRconfined⟩ :=
    local_theta_actual_index h hcomm X hXH hXne hXz hescape hrank beta hbeta hp
  obtain ⟨hWodd, hThetaW, hWconfined, _hpartK, hSylowK⟩ :=
    local_theta_actual_capture h hcomm X hXH hXne hXz hescape hrank beta hbeta hp hpodd
      A0 hA0T hA0p hA0z hnoncentral
  have hnormalization := local_theta_actual_normalization h hcomm X hXH hXne hXz
    hescape hrank beta hbeta hp hpodd A0 hA0T hA0p hA0z hnoncentral
  have hWEU : W ≤ E ⊓ U := hWconfined.trans inf_le_right
  have hThetaE : Theta ≤ E := hThetaW.trans (hWEU.trans inf_le_left)
  have hThetaCanonical : Theta =
      (CFSG.pPrimeCore p ((CFSG.oddCore D).map D.subtype)).map
        ((CFSG.oddCore D).map D.subtype).subtype :=
    generatedPairGrowth_ambient_canonical_core_eq D hp
  have hIclass : I = Subgroup.closure (conjugacyWithin T z) :=
    congrArg Subgroup.closure (localNormalizer_point_class_eq_pair_odd_core_class
      h.local_datum S2 hzS2 hzcenter Y hzY hescape beta hbeta)
  have hKrank : 2 ≤ CFSG.Open.pRank 2 K := by
    rw [← CFSG.ComponentClassification.TwoRankTransport.subgroup K]
    exact numeric_rank_two_of_four hfour
  have hSylowTwo : ∀ S : Sylow 2 K, IsElementaryAbelian 2 (S : Subgroup K) :=
    fun S => htwo _ S.isPGroup'
  have hClassEq : {v : G | v ∈ K ∧ IsInvolution v} = conjugacyWithin T z := by
    ext v
    exact hclass v
  have hWambientOdd : Odd (Nat.card W) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hWodd
  have hWcoprime : Nat.Coprime p (Nat.card W) := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hWnormal : (W.subgroupOf K).Normal := by
    change (((CFSG.pPrimeCore p K).map K.subtype).comap K.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    infer_instance
  refine ⟨hThetaE, hThetaCanonical, hUD, hUnormal, hUodd, hpart,
    hIpoint, hInormal, hzI, hIclass, hKpoint, hKnorm, hsol, hKrank, hSylowTwo,
    hClassEq, hindex, hWambientOdd, hWcoprime, hWnormal, hThetaW, hWEU,
    hUprod, hKprod, hgen, ?_⟩
  intro Q
  let QG := (Q : Subgroup T).map T.subtype
  let ZJ := (orderZJ QG).map QG.subtype
  obtain ⟨S, hSQ⟩ := hSylowK Q
  have hQcanonical : theorem4bIsSylowSubgroupOf p QG K := ⟨S, hSQ.symm⟩
  obtain ⟨hprod, w, hw, hnorm, hwi, hwclass⟩ := hnormalization Q
  exact ⟨hQcanonical, hprod, ⟨rightConjugateElem z w, hwclass, hnorm⟩,
    w, hw, hwi, hwclass, hnorm⟩

end CFSG.ShultStronglyClosedTI
