module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaActualIndex
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaOddCore
public import CFSG.Adapters.QiuzhenLegacy.Compat.G3.RightConjugate

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.OrderReductions.PrimePart

universe u

variable {G : Type u} [Group G] [Finite G]

theorem local_theta_actual_capture
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (A0 : Subgroup G)
    (hA0T : A0 ≤ Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta.val)
    (hA0p : IsPGroup p A0) (hA0z : rightConjugate A0 z = A0)
    (hnoncentral : ¬ A0 ≤ Subgroup.centralizer ({z} : Set G)) :
    let Y := Subgroup.normalizer (X : Set G)
    let D := Y ⊓ pairPointStabilizer H beta.val
    let T := Y ⊓ pairOddCore H beta.val
    let Theta := minimalLocalFailurePairConfinementTheta p D
    let U := T ⊔ Theta
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    let W := CFSG.pPrimeCore p K
    Odd (Nat.card W) ∧ Theta ≤ W.map K.subtype ∧
      W.map K.subtype ≤ Y ⊓ (triplePointStabilizer H z beta.val ⊓ U) ∧
      primePart p (Nat.card U) = primePart p (Nat.card K) ∧
      (∀ Q : Sylow p T, ∃ S : Sylow p K,
        (S : Subgroup K).map K.subtype = (Q : Subgroup T).map T.subtype) := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let D := Y ⊓ pairPointStabilizer H beta.val
  let T := Y ⊓ pairOddCore H beta.val
  let Theta := minimalLocalFailurePairConfinementTheta p D
  let U := T ⊔ Theta
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  let W := CFSG.pPrimeCore p K
  obtain ⟨S2, hzS2, hzcenter⟩ := h.central_sylow
  obtain ⟨_hDpoint, _hTD, _hTnormal, hUD, _hUnormal, _hUodd, _hpart, hSylow,
    _hIpoint, _hInormal, hzI, _hKpoint, _hKnorm, _hIKnormal, _hgen, _hUprod, _hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S2 hzS2 hzcenter Y hzY hescape
      beta hbeta hp
  obtain ⟨hsol, _hfour, _htwo, hclass, _himage⟩ :=
    local_theta_actual_structure h hcomm X hXH hXne hXz hescape hrank beta hbeta hp
  let : Group.IsSolvable K := hsol
  obtain ⟨_hIelem, _hIRU, hindex, hRconfined⟩ :=
    local_theta_actual_index h hcomm X hXH hXne hXz hescape hrank beta hbeta hp
  have hzK : z ∈ K := (le_sup_left : I ≤ K) hzI
  let zK : K := ⟨z, hzK⟩
  have hTK : T ≤ K := (le_sup_left : T ≤ U).trans le_sup_right
  have hA0K : A0 ≤ K := hA0T.trans hTK
  let AK := A0.subgroupOf K
  have hAKp : IsPGroup p AK := hA0p.comap_of_injective K.subtype K.subtype_injective
  have hzAKnorm : zK ∈ Subgroup.normalizer (AK : Set K) :=
    Subgroup.le_normalizer_comap K.subtype (invariant_subgroup_mem_normalizer hA0z)
  have hAKz : rightConjugate AK zK = AK :=
    rightConjugate_eq_self_of_mem_normalizer hzAKnorm
  have hAKnoncentral : ¬ AK ≤ Subgroup.centralizer ({zK} : Set K) := by
    intro hcent
    apply hnoncentral
    intro a ha
    have haK : (⟨a, hA0K ha⟩ : K) ∈ AK := ha
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hcent haK)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc)
  have hclassK : ∀ v : K, IsInvolution v → v ∈ conjugacyWithin (T.subgroupOf K) zK := by
    intro v hv
    have hvG : IsInvolution (v : G) :=
      ⟨fun hv1 => hv.ne_one (Subtype.ext hv1), congrArg Subtype.val hv.sq_eq_one⟩
    have hc := (hclass v.val).mp ⟨v.property, hvG⟩
    rw [← subgroup_class_image K T hTK hzK] at hc
    obtain ⟨a, ha, hav⟩ := hc
    exact K.subtype_injective hav ▸ ha
  have hWodd : Odd (Nat.card W) := prime_complement_core_odd_of_involution_class
    hp (T.subgroupOf K) AK hclassK hAKp hAKz hAKnoncentral
  have hWR : W ≤ CFSG.oddCore K := odd_prime_complement_core_le_odd_core hWodd
  have hWconfined : W.map K.subtype ≤ Y ⊓ (triplePointStabilizer H z beta.val ⊓ U) :=
    (Subgroup.map_mono hWR).trans hRconfined
  have hpartK : primePart p (Nat.card U) = primePart p (Nat.card K) := by
    have hh := prime_part_of_two_power_index hp hpodd (U.subgroupOf K) hindex
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : U ≤ K)).toEquiv] at hh
    exact hh
  have hThetaU : Theta ≤ U := le_sup_right
  have hThetaNormal : (Theta.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hThetaU).mpr
      (hUD.trans (Subgroup.le_normalizer.trans (pairConfinement_theta_normalizer p D)))
  have hThetaW : Theta ≤ W.map K.subtype :=
    normal_prime_complement_le_core_of_full_prime_part hp U K Theta le_sup_right hThetaU
      hThetaNormal (pairConfinement_theta_order p hp D).2 hpartK
  refine ⟨hWodd, hThetaW, hWconfined, hpartK, ?_⟩
  intro Q
  obtain ⟨R, hRQ⟩ := hSylow Q
  let : Fact p.Prime := ⟨hp⟩
  apply exists_sylow_image_of_card p ((Q : Subgroup T).map T.subtype) K
    ((Subgroup.map_subtype_le _).trans hTK)
  rw [← hRQ, sylow_map_card_eq_primePart, hpartK]

end CFSG.ShultStronglyClosedTI.LocalTheta
