module

public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardSigma
public import CFSG.RankThree.GF2n.Parrott.QA45SigmaCentralizers
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassV
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42Centres

import CFSG.RankThree.GF2n.Parrott.SpinConfig

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_jconj_of_involution_of_orderThree (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {y ρ : G} (hyH : y ∈ H z) (hyy : y * y = 1)
    (hdim : fixDimV h ⟨y, hyH⟩ = 4) (hρH : ρ ∈ H z) (hρ3 : ρ * ρ * ρ = 1)
    (hc : y⁻¹ * (ρ * y * ρ⁻¹) ∈ J z) :
    ∃ j₀ ∈ J z, ρ * y * ρ⁻¹ = j₀ * y * j₀⁻¹ := by
  have haa : (ρ * y * ρ⁻¹) * (ρ * y * ρ⁻¹) = 1 := by
    calc (ρ * y * ρ⁻¹) * (ρ * y * ρ⁻¹) = ρ * (y * y) * ρ⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  obtain ⟨k, hkJ, e, heZ, hke⟩ := exists_conj_mul_centerIn_of_fixDimV_eq_four h hyH hc hdim
    (by rw [hyy]; exact (centerIn (J z)).one_mem) (by rw [haa]; exact (centerIn (J z)).one_mem)
  have hee : e * e = 1 := centerIn_J_sq h heZ
  have heZ' : e ∈ centerIn (H z) := by rw [← hZ]; exact heZ
  have heH : ∀ g ∈ H z, g * e = e * g := fun g hg =>
    Subgroup.mem_centralizer_iff.mp heZ'.2 g hg
  have hρe : ρ * e * ρ⁻¹ = e := by rw [heH ρ hρH]; group
  obtain ⟨a, ha⟩ : ∃ a, a = ρ * y * ρ⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ρ * a * ρ⁻¹ := ⟨_, rfl⟩
  obtain ⟨k₁, hk₁⟩ : ∃ k₁, k₁ = ρ * k * ρ⁻¹ := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k₂, k₂ = ρ * k₁ * ρ⁻¹ := ⟨_, rfl⟩
  rw [← ha] at hke
  have hk1 : k₁ * b * k₁⁻¹ = a * e := by
    calc k₁ * b * k₁⁻¹ = ρ * (k * a * k⁻¹) * ρ⁻¹ := by rw [hk₁, hb]; group
      _ = ρ * (y * e) * ρ⁻¹ := by rw [hke]
      _ = (ρ * y * ρ⁻¹) * (ρ * e * ρ⁻¹) := by group
      _ = a * e := by rw [← ha, hρe]
  have hb3 : ρ * b * ρ⁻¹ = y := by
    calc ρ * b * ρ⁻¹ = (ρ * ρ * ρ) * y * (ρ * ρ * ρ)⁻¹ := by rw [hb, ha]; group
      _ = y := by rw [hρ3]; group
  have hk2 : k₂ * y * k₂⁻¹ = b * e := by
    calc k₂ * y * k₂⁻¹ = k₂ * (ρ * b * ρ⁻¹) * k₂⁻¹ := by rw [hb3]
      _ = ρ * (k₁ * b * k₁⁻¹) * ρ⁻¹ := by rw [hk₂]; group
      _ = ρ * (a * e) * ρ⁻¹ := by rw [hk1]
      _ = (ρ * a * ρ⁻¹) * (ρ * e * ρ⁻¹) := by group
      _ = b * e := by rw [← hb, hρe]
  have hk₁J : k₁ ∈ J z := by
    rw [hk₁]
    exact H_conj_mem_J (⟨ρ, hρH⟩ : ↥(H z)) hkJ
  have hk₂J : k₂ ∈ J z := by
    rw [hk₂]
    exact H_conj_mem_J (⟨ρ, hρH⟩ : ↥(H z)) hk₁J
  have hek : e * k₁⁻¹ = k₁⁻¹ * e := (heH _ ((H z).inv_mem (J_le_H hk₁J))).symm
  refine ⟨k₁ * k₂, (J z).mul_mem hk₁J hk₂J, ?_⟩
  rw [← ha]
  calc a = (a * e) * e := by rw [mul_assoc, hee, mul_one]
    _ = (k₁ * b * k₁⁻¹) * e := by rw [hk1]
    _ = k₁ * b * (k₁⁻¹ * e) := by group
    _ = k₁ * b * (e * k₁⁻¹) := by rw [hek]
    _ = k₁ * (b * e) * k₁⁻¹ := by group
    _ = k₁ * (k₂ * y * k₂⁻¹) * k₁⁻¹ := by rw [hk2]
    _ = (k₁ * k₂) * y * (k₁ * k₂)⁻¹ := by group

section Omega

omit [Finite G] in
theorem exists_subgroup_mem_iff_mul_self_eq_one {X : Subgroup G}
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    ∃ K : Subgroup G, ∀ k : G, k ∈ K ↔ k ∈ X ∧ k * k = 1 :=
  ⟨{ carrier := {k | k ∈ X ∧ k * k = 1}
     one_mem' := ⟨X.one_mem, mul_one 1⟩
     mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, by
       calc a * b * (a * b) = a * (b * a) * b := by group
         _ = a * (a * b) * b := by rw [hX b hb.1 a ha.1]
         _ = (a * a) * (b * b) := by group
         _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
     inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by
       have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2
       rw [h1]
       exact ha.2⟩ }, fun _ => Iff.rfl⟩

omit [Finite G] in
theorem normalizer_le_normalizer_of_mem_iff_mul_self {X K : Subgroup G}
    (hK : ∀ k : G, k ∈ K ↔ k ∈ X ∧ k * k = 1) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hn' : ∀ b : G, b ∈ X ↔ n * b * n⁻¹ ∈ X := fun b => by
    have := Subgroup.mem_normalizer_iff.mp hn b
    simpa using this
  have hsq : ∀ b : G, (n * b * n⁻¹) * (n * b * n⁻¹) = n * (b * b) * n⁻¹ := fun b => by group
  show k ∈ K ↔ n * k * n⁻¹ ∈ K
  rw [hK, hK, hn' k]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [hsq, h2]; group⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [hsq] at h2
    calc k * k = n⁻¹ * (n * (k * k) * n⁻¹) * n := by group
      _ = 1 := by rw [h2]; group

omit [Finite G] in
theorem isElemAbelian_two_of_mem_iff {X K : Subgroup G} (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hK : ∀ k : G, k ∈ K ↔ k ∈ X ∧ k * k = 1) : IsElemAbelian 2 K :=
  ⟨⟨⟨fun a b => Subtype.ext (hX a ((hK a).mp a.2).1 b ((hK b).mp b.2).1)⟩⟩, fun k hk => by
    rw [pow_two]
    exact ((hK k).mp hk).2⟩

end Omega

theorem exists_mem_J_centralizer_of_fixed (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) {ρ : ↥(H z)} (hρ : orderOf ρ = 3)
    {v : QuotientV.V z} (hv : conjV h ρ v = v) :
    ∃ (j : G) (hj : j ∈ J z), (ρ : G) * j * (ρ : G)⁻¹ = j ∧ QuotientV.pi z ⟨j, hj⟩ = v := by
  obtain ⟨c₁, rfl⟩ := QuotientV.pi_surjective z v
  rw [conjV_mk] at hv
  have hcent : ∀ e ∈ centerIn (J z), ∀ g ∈ H z, g * e = e * g := fun e he g hg =>
    mem_centralizer_iff.mp ((hZ ▸ he : e ∈ centerIn (H z))).2 g hg
  have h1 : QuotientV.pi z ((c₁)⁻¹ * conjJ' z ρ c₁) = 1 := by
    rw [map_mul, map_inv, hv, inv_mul_cancel]
  have hcoset : (c₁ : G)⁻¹ * ((ρ : G) * (c₁ : G) * (ρ : G)⁻¹) ∈ centerIn (J z) := by
    have h2 := (pi_eq_one_iff_mem_centerIn (z := z) (x := ((c₁)⁻¹ * conjJ' z ρ c₁ : J z))
      ((c₁)⁻¹ * conjJ' z ρ c₁).2).mp h1
    simpa [conjJ'_apply_coe] using h2
  have hN' : ∀ x ∈ centerIn (J z), (ρ : G) * x * (ρ : G)⁻¹ ∈ centerIn (J z) := fun x hx => by
    have : (ρ : G) * x * (ρ : G)⁻¹ = x := by
      have := hcent x hx ρ ρ.2
      calc (ρ : G) * x * (ρ : G)⁻¹ = (x * (ρ : G)) * (ρ : G)⁻¹ := by rw [this]
        _ = x := by group
    rw [this]
    exact hx
  have hcop : Nat.Coprime (orderOf (ρ : G)) (Nat.card (centerIn (J z))) := by
    rw [Subgroup.orderOf_coe, hρ, card_centerIn_J h]
    norm_num
  obtain ⟨e, heZ, hfix⟩ := exists_fixed_mem_coset_of_coprime (centerIn (J z)) hN' hcoset hcop
  have hcJ : (c₁ : G) * e ∈ J z := (J z).mul_mem c₁.2 heZ.1
  refine ⟨(c₁ : G) * e, hcJ, hfix, ?_⟩
  have : QuotientV.pi z (⟨e, heZ.1⟩ : J z) = 1 := (pi_eq_one_iff_mem_centerIn heZ.1).mpr heZ
  have h3 : (⟨(c₁ : G) * e, hcJ⟩ : J z) = c₁ * ⟨e, heZ.1⟩ := rfl
  rw [h3, map_mul, this, mul_one]

section A45Part

open CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

theorem qa45_closure_t_uv_elements {e : A45} (he : e ∈ Subgroup.closure ({tA, uA * vA} : Set A45)) :
    e = 1 ∨ e = tA ∨ e = uA * vA ∨ e = tA * (uA * vA) := by
  have hA : Nat.card A45 = 51840 := card_QA45
  obtain ⟨hC1, hC2, hC3, hC4⟩ := qa45_involution_centralizers
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have htuv : Commute tA (uA * vA) := hut.mul_right hvt
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have huvsq : (uA * vA) * (uA * vA) = 1 := by
    rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
  have ht1 : tA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC1, hA]; omega)
  have huv1 : uA * vA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC4, hA]; omega)
  have hne : tA ≠ uA * vA := fun h => by
    have h' := hC4
    rw [← h, hC1] at h'
    omega
  have hset := CFSG.GroupTheory.coe_closure_pair_eq htt huvsq htuv.eq ht1 huv1 hne
  have hmem : e ∈ (Subgroup.closure ({tA, uA * vA} : Set A45) : Set A45) := he
  rw [hset] at hmem
  simpa using hmem

theorem qa45_two_element_classes {a : A45}
    (ha : a ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ⊓
      Subgroup.centralizer ({uA * vA * tA} : Set A45))
    (h2 : ∃ m : ℕ, orderOf a = 2 ^ m) :
    a = 1 ∨ IsConj a tA ∨ IsConj a (uA * vA) ∨ a = uA * vA * tA := by
  obtain ⟨c, -, hcE⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer ha.1 h2
  obtain ⟨-, hEelem, -⟩ := qa45_sigma_centralizer_sylow.2.1
  have hsq : c * a * c⁻¹ * (c * a * c⁻¹) = 1 := hEelem.mul_self_eq_one hcE
  have haa : a * a = 1 := by
    calc a * a = c⁻¹ * (c * a * c⁻¹ * (c * a * c⁻¹)) * c := by group
      _ = 1 := by rw [hsq]; group
  obtain ⟨d, hdC, hdE⟩ := exists_conj_mem_closure_t_uv_of_mem_centralizer_uvt ha haa
  have hda : a = d * (d⁻¹ * a * d) * d⁻¹ := by group
  have hdu : d * (uA * vA * tA) = (uA * vA * tA) * d :=
    Subgroup.mem_centralizer_singleton_iff.mp hdC.2
  rcases qa45_closure_t_uv_elements hdE with h1 | h1 | h1 | h1
  · left
    rw [hda, h1]
    group
  · right
    left
    exact isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv]; exact h1⟩
  · right
    right
    left
    exact isConj_iff.mpr ⟨d⁻¹, by rw [inv_inv]; exact h1⟩
  · right
    right
    right
    have htc : tA * (uA * vA) = uA * vA * tA := by
      have hut : Commute tA uA := Subtype.ext t_commute_u
      have hvt : Commute tA vA := Subtype.ext t_commute_v
      exact (hut.mul_right hvt).eq
    rw [hda, h1, htc]
    calc d * (uA * vA * tA) * d⁻¹ = (uA * vA * tA) * d * d⁻¹ := by rw [hdu]
      _ = uA * vA * tA := by group

end A45Part

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

open CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

theorem isConj_vA_uvt : IsConj vA (uA * vA * tA) := isConj_iff.mpr ⟨bA, conj_v_uvt_QA45⟩

theorem uvt_commute_s1A_mul_s2A_inv :
    (uA * vA * tA) * (s1A * s2A⁻¹) = (s1A * s2A⁻¹) * (uA * vA * tA) :=
  Subtype.ext uvt_mul_sigma1_mul_sigma2_inv

theorem qa45_v_ne_one : vA ≠ 1 := by
  obtain ⟨-, -, hC3, -⟩ := qa45_involution_centralizers
  exact CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC3, card_QA45]; omega)

theorem exists_conj_mem_centralizer_of_class_v (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hV3 : ∀ y : ↥(H z), IsConj (qH D y) vA → fixDimV h y = 4)
    {ρ : ↥(H z)} (hρ3 : orderOf ρ = 3) (hqρ : qH D ρ = s1A * s2A⁻¹)
    {y : G} (hy : y ∈ H z) (hyy : y * y = 1) (hyc : IsConj (qH D ⟨y, hy⟩) vA) :
    ∃ c ∈ H z, ∃ x : G, ∃ hx : x ∈ H z, x ∈ centralizer ({(ρ : G)} : Set G) ∧ x * x = 1 ∧
      qH D ⟨x, hx⟩ = uA * vA * tA ∧ c * y * c⁻¹ = x := by
  have hρG3 : (ρ : G) * ρ * ρ = 1 := by
    have h1 : ρ * ρ * ρ = 1 := by
      have h2 := pow_orderOf_eq_one ρ
      rwa [hρ3, pow_three'] at h2
    exact congrArg Subtype.val h1
  have hρG3' : orderOf (ρ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hρ3
  obtain ⟨a, ha⟩ := isConj_iff.mp (hyc.trans isConj_vA_uvt)
  obtain ⟨c₁, hc₁⟩ := qH_surjective D a
  obtain ⟨Y, hY⟩ : ∃ Y : ↥(H z), Y = c₁ * ⟨y, hy⟩ * c₁⁻¹ := ⟨_, rfl⟩
  have hqY : qH D Y = uA * vA * tA := by
    rw [hY, map_mul, map_mul, map_inv, hc₁]
    exact ha
  have hYcoe : (Y : G) = (c₁ : G) * y * (c₁ : G)⁻¹ := by rw [hY]; rfl
  have hYY : (Y : G) * Y = 1 := by
    rw [hYcoe]
    calc (c₁ : G) * y * (c₁ : G)⁻¹ * ((c₁ : G) * y * (c₁ : G)⁻¹)
        = (c₁ : G) * (y * y) * (c₁ : G)⁻¹ := by group
      _ = 1 := by rw [hyy]; group
  have hdim : fixDimV h Y = 4 := hV3 Y (by rw [hqY]; exact isConj_vA_uvt.symm)
  have hc : (Y : G)⁻¹ * ((ρ : G) * Y * (ρ : G)⁻¹) ∈ J z := by
    have h1 : Y⁻¹ * (ρ * Y * ρ⁻¹) ∈ (J z).subgroupOf (H z) := by
      refine (J_mem_iff D _).mpr ?_
      have hcomm : (s1A * s2A⁻¹) * (uA * vA * tA) * (s1A * s2A⁻¹)⁻¹ = uA * vA * tA := by
        rw [← uvt_commute_s1A_mul_s2A_inv]
        group
      simp only [map_mul, map_inv, hqY, hqρ]
      rw [hcomm, inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨j₀, hj₀J, hj₀⟩ := exists_jconj_of_involution_of_orderThree h hZ Y.2 hYY hdim ρ.2 hρG3 hc
  obtain ⟨j, hjJ, hj⟩ := exists_jconj_commute_of_orderOf_three (isPGroup_J h) ρ.2 hρG3' hj₀J hj₀
  have hjH : j ∈ H z := J_le_H hjJ
  have hxH : j * (Y : G) * j⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem hjH Y.2) ((H z).inv_mem hjH)
  refine ⟨j * (c₁ : G), (H z).mul_mem hjH c₁.2, j * (Y : G) * j⁻¹, hxH,
    mem_centralizer_singleton_iff.mpr hj.symm, ?_, ?_, ?_⟩
  · calc j * (Y : G) * j⁻¹ * (j * (Y : G) * j⁻¹) = j * ((Y : G) * Y) * j⁻¹ := by group
      _ = 1 := by rw [hYY]; group
  · have hjq : qH D ⟨j, hjH⟩ = 1 := (J_mem_iff D ⟨j, hjH⟩).mp hjJ
    have h1 : (⟨j * (Y : G) * j⁻¹, hxH⟩ : ↥(H z)) = ⟨j, hjH⟩ * Y * ⟨j, hjH⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hjq, hqY]
    group
  · calc j * (c₁ : G) * y * (j * (c₁ : G))⁻¹ = j * ((c₁ : G) * y * (c₁ : G)⁻¹) * j⁻¹ := by group
      _ = j * (Y : G) * j⁻¹ := by rw [hYcoe]

theorem inv_mul_mem_J_or_isConj_of_mem_X {ρ : ↥(H z)} (hqρ : qH D ρ = s1A * s2A⁻¹) {x : G}
    (hxH : x ∈ H z) (hqx : qH D ⟨x, hxH⟩ = uA * vA * tA) {X : Subgroup G}
    (hX : IsSylowOf 2 X (centralizer ({(ρ : G)} : Set G) ⊓ H z ⊓ centralizer ({x} : Set G))) :
    ∀ k ∈ X, k ∉ J z → x⁻¹ * k ∈ J z ∨
      ∃ hk : k ∈ H z, IsConj (qH D ⟨k, hk⟩) tA ∨ IsConj (qH D ⟨k, hk⟩) (uA * vA) := by
  intro k hkX hkJ
  obtain ⟨⟨hkρ, hkH⟩, hkx⟩ := hX.le hkX
  have h2el : ∃ m : ℕ, orderOf (qH D ⟨k, hkH⟩) = 2 ^ m := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hX.isPGroup) ⟨k, hkX⟩
    have hdvd : orderOf (qH D ⟨k, hkH⟩) ∣ 2 ^ m := by
      rw [← hm]
      have h3 : orderOf (qH D ⟨k, hkH⟩) ∣ orderOf (⟨k, hkH⟩ : ↥(H z)) := orderOf_map_dvd _ _
      have h4 : orderOf (⟨k, hkH⟩ : ↥(H z)) = orderOf (⟨k, hkX⟩ : ↥X) := by
        rw [← Subgroup.orderOf_coe (⟨k, hkH⟩ : ↥(H z)), ← Subgroup.orderOf_coe (⟨k, hkX⟩ : ↥X)]
      exact h3.trans (h4 ▸ dvd_rfl)
    obtain ⟨m', -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m', hm'⟩
  have hcomm : qH D ⟨k, hkH⟩ ∈ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) := by
    rw [← hqρ, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (qH D) (Subtype.ext (mem_centralizer_singleton_iff.mp hkρ))
  have hcommx : qH D ⟨k, hkH⟩ ∈ Subgroup.centralizer ({uA * vA * tA} : Set A45) := by
    rw [← hqx, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg (qH D) (Subtype.ext (mem_centralizer_singleton_iff.mp hkx))
  rcases qa45_two_element_classes ⟨hcomm, hcommx⟩ h2el with h1 | h1 | h1 | h1
  · exact absurd ((J_mem_iff D ⟨k, hkH⟩).mpr h1) hkJ
  · exact Or.inr ⟨hkH, Or.inl h1⟩
  · exact Or.inr ⟨hkH, Or.inr h1⟩
  · left
    have h3 : qH D ((⟨x, hxH⟩ : ↥(H z))⁻¹ * ⟨k, hkH⟩) = 1 := by
      rw [map_mul, map_inv, hqx, h1]
      group
    exact (J_mem_iff D _).mpr h3

theorem exists_mem_J_inf_centralizer_not_commute (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {ρ : ↥(H z)} (hρ : orderOf ρ = 3) (hqρ : qH D ρ = s1A * s2A⁻¹) {x : G} (hxH : x ∈ H z)
    (hqx : qH D ⟨x, hxH⟩ = uA * vA * tA) :
    ∃ j ∈ J z ⊓ centralizer ({(ρ : G)} : Set G), x * j ≠ j * x := by
  by_contra hcon
  push Not at hcon
  have hXfix : ∀ v : QuotientV.V z, conjV h ρ v = v → conjV h ⟨x, hxH⟩ v = v := by
    intro v hv
    obtain ⟨j, hj, hρj, rfl⟩ := exists_mem_J_centralizer_of_fixed h hZ hρ hv
    have hjρ : j * (ρ : G) = ρ * j := by
      calc j * (ρ : G) = ((ρ : G) * j * (ρ : G)⁻¹) * ρ := by rw [hρj]
        _ = (ρ : G) * j := by group
    have hxj : x * j = j * x := hcon j ⟨hj, mem_centralizer_singleton_iff.mpr hjρ⟩
    rw [conjV_pi_conj h ⟨x, hxH⟩ hj]
    congr 1
    apply Subtype.ext
    show x * j * x⁻¹ = j
    calc x * j * x⁻¹ = (j * x) * x⁻¹ := by rw [hxj]
      _ = j := by group
  have hle : autFixedSubgroup (conjV h ρ) ≤ autFixedSubgroup (conjV h (ρ * ⟨x, hxH⟩)) := by
    intro v hv
    rw [mem_autFixedSubgroup] at hv ⊢
    rw [map_mul, MulAut.mul_apply, hXfix v hv, hv]
  have hcard := Subgroup.card_le_of_le hle
  rw [card_fix h ρ, card_fix h (ρ * ⟨x, hxH⟩)] at hcard
  have hdim4 : fixDimV h ρ = 4 := by
    have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP ρ
    rw [hqρ, spinFixedCard_sigma1_mul_sigma2_inv] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have htc : tA * (uA * vA) = uA * vA * tA := (hut.mul_right hvt).eq
  have hmemE : uA * vA * tA ∈ Subgroup.closure ({tA, uA * vA} : Set A45) := by
    rw [← htc]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have huvt1 : uA * vA * tA ≠ 1 := fun h1 =>
    qa45_v_ne_one (isConj_one_left.mp (h1 ▸ isConj_vA_uvt))
  have hfix2 := spinFixedCard_sigma1_mul_sigma2_inv_mul hmemE huvt1
  have hdim2 : fixDimV h (ρ * ⟨x, hxH⟩) = 2 := by
    have h1 := two_pow_fixDimV_eq_of_conj_rep D h rhoA P hP (ρ * ⟨x, hxH⟩)
    rw [map_mul, hqρ, hqx, hfix2] at h1
    exact Nat.pow_right_injective (le_refl 2) (h1.trans (by norm_num))
  rw [hdim4, hdim2] at hcard
  have h16 : 2 ^ 4 ≤ 2 ^ 2 := hcard
  omega

end Certified

end CFSG.RankThree.GF2n.Parrott
