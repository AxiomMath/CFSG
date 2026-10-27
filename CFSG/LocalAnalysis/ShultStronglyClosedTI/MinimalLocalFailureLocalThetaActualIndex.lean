module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaIntersection
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaConfinement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaIndex

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

theorem subgroup_class_image (K T : Subgroup G) (hTK : T ≤ K)
    {z : G} (hzK : z ∈ K) :
    K.subtype '' conjugacyWithin (T.subgroupOf K) (⟨z, hzK⟩ : K) =
      conjugacyWithin T z := by
  apply Set.Subset.antisymm
  · rintro a ⟨b, ⟨t, rfl⟩, rfl⟩
    exact ⟨⟨t.val.val, t.property⟩, rfl⟩
  · rintro a ⟨t, rfl⟩
    let tK : K := ⟨t.val, hTK t.property⟩
    let tT : T.subgroupOf K := ⟨tK, t.property⟩
    exact ⟨tK⁻¹ * ⟨z, hzK⟩ * tK, ⟨tT, rfl⟩, rfl⟩

theorem local_theta_actual_index [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (X : Subgroup G) (hXH : X ≤ H) (hXne : X ≠ ⊥)
    (hXz : rightConjugate X z = X)
    (hescape : ¬ Subgroup.normalizer (X : Set G) ≤ H)
    (hrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin (Subgroup.normalizer (X : Set G)) z)))
    (beta : numeratorRightOrbit H (Subgroup.normalizer (X : Set G)) (rightCosetMk H 1))
    (hbeta : beta.val ≠ rightCosetMk H 1) {p : ℕ} (hp : p.Prime) :
    let Y := Subgroup.normalizer (X : Set G)
    let D := Y ⊓ pairPointStabilizer H beta.val
    let T := Y ⊓ pairOddCore H beta.val
    let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
    let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
    let K := I ⊔ U
    let R := CFSG.oddCore K
    IsElementaryAbelian 2 ((I.subgroupOf K).map (QuotientGroup.mk' R)) ∧
      I ⊓ R.map K.subtype ≤ U ∧
      (∃ n : ℕ, U.relIndex K = 2 ^ n) ∧
      R.map K.subtype ≤ Y ⊓ (triplePointStabilizer H z beta.val ⊓ U) := by
  let Y := Subgroup.normalizer (X : Set G)
  have hzY : z ∈ Y := invariant_subgroup_mem_normalizer hXz
  let zY : Y := ⟨z, hzY⟩
  let L := involutionPointHull zY
  let D := Y ⊓ pairPointStabilizer H beta.val
  let T := Y ⊓ pairOddCore H beta.val
  let U := T ⊔ minimalLocalFailurePairConfinementTheta p D
  let I := Subgroup.closure (conjugacyWithin (H ⊓ Y) z)
  let K := I ⊔ U
  let UY := U.subgroupOf Y
  let F := L ⊔ UY
  let R := CFSG.oddCore K
  let RA := R.map K.subtype
  let B := pairPointStabilizer H beta.val
  let J := pairOddCore H beta.val
  let E := triplePointStabilizer H z beta.val
  let V := (CFSG.oddCore E).map E.subtype
  let N := RA ⊓ J
  let IK := I.subgroupOf K
  let UK := U.subgroupOf K
  let NK := N.subgroupOf K
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨_hDpoint, _hTD, _hTnormal, hUD, _hUnormal, hUodd, _hpart, _hSylow,
    _hIpoint, _hInormal, hzI, _hKpoint, _hKnorm, hIKnormal, hgen, _hUprod, _hKprod⟩ :=
    local_theta_auxiliary_construction h.local_datum S hzS hzcenter Y hzY hescape beta hbeta hp
  let : IK.Normal := hIKnormal
  have hzK : z ∈ K := (le_sup_left : I ≤ K) hzI
  let zK : K := ⟨z, hzK⟩
  have hTK : T ≤ K := (le_sup_left : T ≤ U).trans le_sup_right
  have hRK : RA ≤ K := Subgroup.map_subtype_le _
  have hRE : RA ≤ Y ⊓ E := local_theta_odd_core_le_triple h hcomm X hXH hXne hXz
    hescape hrank beta hbeta hp
  have hNV : N = RA ⊓ V := by
    dsimp only [N, V, E, J]
    rw [triple_odd_core_eq_pair_intersection h.local_datum S hzS hzcenter beta.val hbeta]
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hx.2, (hRE hx.1).2⟩
    · intro x hx
      exact ⟨hx.1, hx.2.1⟩
  have hRnorm : K ≤ Subgroup.normalizer (RA : Set G) :=
    Subgroup.le_normalizer.trans (generatedPairGrowth_normalizer_le_characteristic_image
      K R (CFSG.ComponentClassification.OddCore.characteristic K))
  have hJnorm : B ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.le_normalizer.trans (generatedPairGrowth_normalizer_le_characteristic_image
      B (CFSG.oddCore B) (CFSG.ComponentClassification.OddCore.characteristic B))
  have hUnorm : U ≤ Subgroup.normalizer (N : Set G) :=
    (le_inf ((le_sup_right : U ≤ K).trans hRnorm)
      (hUD.trans (inf_le_right.trans hJnorm))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hzV : z ∈ Subgroup.normalizer (V : Set G) :=
    (generatedPairGrowth_normalizer_le_characteristic_image E (CFSG.oddCore E)
      (CFSG.ComponentClassification.OddCore.characteristic E))
      (triple_stabilizer_normalized_by_distinguished h.local_datum beta.val)
  have hzN : z ∈ Subgroup.normalizer (N : Set G) := by
    rw [hNV]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hRnorm hzK, hzV⟩
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) := by
    change K = Subgroup.zpowers z ⊔ U at hgen
    rw [hgen]
    exact sup_le (Subgroup.zpowers_le.mpr hzN) hUnorm
  have hNK : N ≤ K := inf_le_left.trans hRK
  let : NK.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hNnorm
  have hNR : NK ≤ R := by
    intro a ha
    have haR : a.val ∈ RA := ha.1
    obtain ⟨r, hr, hra⟩ := Subgroup.mem_map.mp haR
    have hraK : r = a := K.subtype_injective hra
    exact hraK ▸ hr
  have hRcomm : ∀ r ∈ R, ⁅r, zK⁆ ∈ NK := by
    intro r hr
    have hcommR : ⁅r, zK⁆ ∈ R := (Subgroup.commutator_le_left R ⊤)
      (Subgroup.commutator_mem_commutator hr (Subgroup.mem_top zK))
    have hcommRA : ((⁅r, zK⁆ : K) : G) ∈ RA := Subgroup.mem_map.mpr ⟨⁅r, zK⁆, hcommR, rfl⟩
    have hrRA : (r : G) ∈ RA := Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    have hcommV : ((⁅r, zK⁆ : K) : G) ∈ V :=
      triple_distinguished_commutator_mem_odd_core h.local_datum S hzS hzcenter
        beta.val hbeta (hRE hrRA).2
    change ((⁅r, zK⁆ : K) : G) ∈ N
    rw [hNV]
    exact ⟨hcommRA, hcommV⟩
  obtain ⟨_hsol, _hKrank, _htwo, _hclass, kF, _hkinj, _hkcomp, hkernel,
    helem, _hcoreimage⟩ := local_theta_actual_structure h hcomm X hXH hXne hXz
      hescape hrank beta hbeta hp
  let qF : K →* F ⧸ CFSG.oddCore F :=
    (QuotientGroup.mk' (CFSG.oddCore F)).comp kF
  have hkernelR : qF.ker ≤ R := by
    unfold R CFSG.oddCore
    exact le_sSup ⟨MonoidHom.normal_ker qF, hkernel⟩
  let : IsElementaryAbelian 2 (IK.map qF) := helem
  have hIelem : IsElementaryAbelian 2 (IK.map (QuotientGroup.mk' R)) :=
    elementary_image_descends_quotient qF IK R hkernelR
  let : IsElementaryAbelian 2 (IK.map (QuotientGroup.mk' R)) := hIelem
  let TK := T.subgroupOf K
  let sK := conjugacyWithin TK zK
  let CK := Subgroup.closure sK
  have hclass := localNormalizer_point_class_eq_pair_odd_core_class h.local_datum
    S hzS hzcenter Y hzY hescape beta hbeta
  have hCK : CK = IK := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_closure, subgroup_class_image K T hTK hzK, ← hclass,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : I ≤ K)]
  have hcentral := normal_quotient_class_centralizer R NK TK hRcomm
  have hsquare : ∀ a ∈ sK, a ^ 2 = 1 := by
    rintro a ⟨t, rfl⟩
    have hzsquare : zK ^ 2 = 1 := Subtype.ext
      (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).1
    calc
      (t.val⁻¹ * zK * t.val) ^ 2 = t.val⁻¹ * zK ^ 2 * t.val := by
        simp only [pow_two, mul_assoc, mul_inv_cancel_left]
      _ = 1 := by rw [hzsquare]; group
  have hRodd : Odd (Nat.card R) := CFSG.ComponentClassification.OddCore.odd_card K
  have hinterK : IK ⊓ R ≤ NK := by
    rw [← hCK]
    let : IsElementaryAbelian 2 (CK.map (QuotientGroup.mk' R)) := hCK.symm ▸ hIelem
    exact odd_central_class_image_intersection_le R NK hNR hRodd sK hsquare hcentral
  have hNU : N ≤ U := by
    intro a ha
    exact (le_sup_left : T ≤ U) ⟨(hRE ha.1).1, ha.2⟩
  have hNKlU : NK ≤ UK := by
    intro a ha
    exact hNU ha
  have hinterU : IK ⊓ R ≤ UK := hinterK.trans hNKlU
  have hUKodd : Odd (Nat.card UK) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : U ≤ K)).toEquiv]
    exact hUodd
  have hIKUK : IK ⊔ UK = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self K
  have hindex : ∃ n : ℕ, UK.index = 2 ^ n :=
    odd_kernel_elementary_factor_index IK UK R hUKodd hIKUK hinterU
  have hRU : R ≤ UK := odd_normal_le_of_two_power_index R UK hRodd hindex
  have hRAU : RA ≤ U := by
    rintro a ⟨r, hr, rfl⟩
    exact hRU hr
  have hinter : I ⊓ RA ≤ U := by
    intro a ha
    let aK : K := ⟨a, (le_sup_left : I ≤ K) ha.1⟩
    have haR : aK ∈ R := by
      obtain ⟨r, hr, hra⟩ := Subgroup.mem_map.mp ha.2
      exact (K.subtype_injective hra : r = aK) ▸ hr
    exact hinterU ⟨ha.1, haR⟩
  exact ⟨hIelem, hinter, hindex, le_inf (hRE.trans inf_le_left)
    (le_inf (hRE.trans inf_le_right) hRAU)⟩

end CFSG.ShultStronglyClosedTI.LocalTheta
