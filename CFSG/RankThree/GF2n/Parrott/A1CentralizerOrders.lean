module

public import CFSG.RankThree.GF2n.Parrott.Section3RemarksU
public import Certificates.Certificate946017
import CFSG.RankThree.GF2n.Parrott.A1LocalData
import CFSG.RankThree.GF2n.Parrott.A1ModelFacts

public section

namespace CFSG.RankThree.GF2n.Parrott.Remarks

open CFSG CFSG.Open CFSG.RankThree.GF2n.Parrott
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)

private theorem card_eq_card_ker_inf_mul_card_map {M Q : Type*} [Group M] [Group Q]
    (φ : M →* Q) (K : Subgroup M) :
    Nat.card K = Nat.card ↥(φ.ker ⊓ K) * Nat.card ↥(K.map φ) := by
  have h := Subgroup.card_map_of_injective (K := φ.ker.subgroupOf K) K.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype] at h
  rw [h, ← MonoidHom.ker_domRestrict, ← MonoidHom.domRestrict_range,
    Subgroup.card_ker_mul_card_range]

private theorem card_le_two_of_forall_eq_one_or_eq {M : Type*} [Group M] [Finite M]
    {X : Subgroup M} {c : M} (hc : c * c = 1) (hX : ∀ x ∈ X, x = 1 ∨ x = c) :
    Nat.card X ≤ 2 := by
  have hle : X ≤ Subgroup.zpowers c := fun x hx => by
    rcases hX x hx with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
  calc Nat.card X ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hle
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hc)

private theorem q8_eq_one_or_eq_a_two {q : QuaternionGroup 2} (hq : q * q = 1) :
    q = 1 ∨ q = QuaternionGroup.a 2 := by
  revert q
  decide

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem card_le_of_isPGroup_two {S K : Subgroup G} (hSK : S ≤ K) (hS : IsPGroup 2 S)
    {a m : ℕ} (hK : Nat.card K = 2 ^ a * m) (hm : Odd m) : Nat.card S ≤ 2 ^ a := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hdvd : 2 ^ n ∣ 2 ^ a * m := by
    rw [← hn, ← hK]
    exact Subgroup.card_dvd_of_le hSK
  rw [hn]
  exact Nat.le_of_dvd (by positivity)
    ((Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right hdvd)

private theorem map_ker_inf_centralizer_eq_CJ {Q : Type*} [Group Q] (φ : ↥(H z) →* Q)
    (hker : φ.ker = (J z).subgroupOf (H z)) (x : ↥(H z)) :
    (φ.ker ⊓ Subgroup.centralizer ({x} : Set ↥(H z))).map (H z).subtype = CJ z (x : G) := by
  ext g
  rw [Subgroup.mem_map, mem_CJ]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.mp hc
    rw [hker] at hcK
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hcC)),
      Subgroup.mem_subgroupOf.mp hcK⟩
  · rintro ⟨hgx, hgJ⟩
    refine ⟨⟨g, J_le_H hgJ⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [hker, Subgroup.mem_subgroupOf]
      exact hgJ
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgx))

theorem map_centralizer_eq_of_orderOf_eq_three (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*}
    [Group Q] (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {x : ↥(H z)}
    (hx : orderOf x = 3) :
    (Subgroup.centralizer ({x} : Set ↥(H z))).map φ =
      φ.range ⊓ Subgroup.centralizer ({φ x} : Set Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hq
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    refine Subgroup.mem_inf.mpr ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, hc', map_mul]
  · intro q hq
    obtain ⟨⟨m₀, rfl⟩, hq⟩ := Subgroup.mem_inf.mp hq
    replace hq := Subgroup.mem_centralizer_singleton_iff.mp hq
    have hP : IsPGroup 3 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    have hker3 : ¬ 3 ∣ Nat.card ↥(φ.ker ⊓ ⊤) := by
      rw [inf_top_eq]
      obtain ⟨n, hn⟩ := (isPGroup_ker_of_ker_eq hcard φ hker).exists_card_eq
      rw [hn]
      intro h
      have h3 := Nat.prime_three.dvd_of_dvd_pow h
      norm_num at h3
    obtain ⟨m, -, hm, hmc⟩ := exists_commute_mem_fibre φ hP le_top hker3 (Subgroup.mem_top m₀)
      fun g hg => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        rw [map_zpow]
        exact ((show Commute (φ m₀) (φ x) from hq).symm.zpow_left k).eq
    exact Subgroup.mem_map.mpr
      ⟨m, Subgroup.mem_centralizer_singleton_iff.mpr (hmc x (Subgroup.mem_zpowers x)).symm, hm⟩

theorem card_H_inf_centralizer_eq (hcard : Nat.card (J z) = 2 ^ 9) {Q : Type*} [Group Q]
    (φ : ↥(H z) →* Q) (hker : φ.ker = (J z).subgroupOf (H z)) {x : ↥(H z)}
    (hx : orderOf x = 3) :
    Nat.card ↥(H z ⊓ Subgroup.centralizer ({(x : G)} : Set G)) =
      Nat.card ↥(CJ z (x : G)) * Nat.card ↥(φ.range ⊓ Subgroup.centralizer ({φ x} : Set Q)) := by
  have hmap : (Subgroup.centralizer ({x} : Set ↥(H z))).map (H z).subtype =
      H z ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    ext g
    rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      exact ⟨c.2, congrArg Subtype.val hc⟩
    · rintro ⟨hg, hgx⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hgx
  have h1 : Nat.card ↥(H z ⊓ Subgroup.centralizer ({(x : G)} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set ↥(H z))) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (H z).subtype_injective
  have h2 : Nat.card ↥(CJ z (x : G)) =
      Nat.card ↥(φ.ker ⊓ Subgroup.centralizer ({x} : Set ↥(H z))) := by
    rw [← map_ker_inf_centralizer_eq_CJ φ hker x]
    exact Subgroup.card_map_of_injective (H z).subtype_injective
  rw [h1, h2, ← map_centralizer_eq_of_orderOf_eq_three hcard φ hker hx]
  exact card_eq_card_ker_inf_mul_card_map φ _

section Model

set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : ↥QA45.originalSubgroup)
set_option quotPrecheck false in
local notation "Pp" => QP45.originalSubgroup.subgroupOf QA45.originalSubgroup

private theorem map_inclusion_centralizer (x : ↥QP45.originalSubgroup) :
    (Subgroup.centralizer ({x} : Set ↥QP45.originalSubgroup)).map
        (Subgroup.inclusion QP45_le_QA45) =
      Pp ⊓ Subgroup.centralizer
        ({Subgroup.inclusion QP45_le_QA45 x} : Set ↥QA45.originalSubgroup) := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    exact ⟨c.2, by rw [← map_mul, hc, map_mul]⟩
  · rintro ⟨hgP, hg⟩
    refine ⟨⟨g, hgP⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.inclusion_injective QP45_le_QA45 (by rw [map_mul, map_mul]; exact hg)

theorem card_QP45_inf_centralizer_sigma1_mul_sigma2_inv :
    Nat.card ↥(Pp ⊓ Subgroup.centralizer ({s1A * s2A⁻¹} : Set ↥QA45.originalSubgroup)) = 54 := by
  have h := Subgroup.card_map_of_injective
    (K := Subgroup.centralizer ({(⟨sigma1, sigma1_mem_Q⟩ : ↥QP45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_Q⟩ : ↥QP45.originalSubgroup)⁻¹} : Set ↥QP45.originalSubgroup))
    (Subgroup.inclusion_injective QP45_le_QA45)
  rw [map_inclusion_centralizer, qp45_card_centralizer_s1s2inv] at h
  exact h

theorem card_QP45_inf_centralizer_sigma1_mul_sigma2 :
    Nat.card ↥(Pp ⊓ Subgroup.centralizer ({s1A * s2A} : Set ↥QA45.originalSubgroup)) = 108 := by
  have hK : Nat.card (Subgroup.centralizer ({s1A * s2A} : Set ↥QA45.originalSubgroup)) = 216 :=
    (card_centralizer_QA45_eq_filter (sigma1 * sigma2)
      (QA45.originalSubgroup.mul_mem sigma1_mem_A sigma2_mem_A)).trans
      Certificates.certificate946005.centralizer_sigma1sigma2
  have hwK : vA * bA ∈ Subgroup.centralizer ({s1A * s2A} : Set ↥QA45.originalSubgroup) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext qa45L1Facts.vbeta_commutes_sigma1_sigma2)
  have hbP : bA ∈ Pp := Subgroup.mem_subgroupOf.mpr beta_mem_Q
  have hwP : vA * bA ∉ Pp := by
    intro h
    have h1 : vA * bA * bA⁻¹ ∈ Pp := mul_mem h (inv_mem hbP)
    rw [mul_inv_cancel_right, Subgroup.mem_subgroupOf] at h1
    exact v_not_mem_Q h1
  have hrel : (Pp).relIndex
      (Subgroup.centralizer ({s1A * s2A} : Set ↥QA45.originalSubgroup)) = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨vA * bA, hwK, hwP, fun b _ => ?_⟩
    by_cases hb : b ∈ Pp
    · exact Or.inr hb
    · left
      rw [Subgroup.mul_mem_iff_of_index_two index_QP45]
      exact iff_of_false hb hwP
  have h := Subgroup.relIndex_mul_card (Pp)
    (Subgroup.centralizer ({s1A * s2A} : Set ↥QA45.originalSubgroup))
  rw [hrel, hK] at h
  omega

private theorem s1A_mul_s2A_inv_ne_one : s1A * s2A⁻¹ ≠ 1 := by
  intro h
  have h54 := card_QP45_inf_centralizer_sigma1_mul_sigma2_inv
  have htop : Subgroup.centralizer ({(1 : ↥QA45.originalSubgroup)} :
      Set ↥QA45.originalSubgroup) = ⊤ := by simp
  rw [h, htop, inf_top_eq, card_QP45_subgroupOf] at h54
  omega

private theorem a2A_pow_four : a2A ^ 4 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact alpha2_pow_four)

private theorem b2A_conj_a2A : b2A * a2A * b2A⁻¹ = a2A⁻¹ := by
  apply Subtype.ext
  show beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹
  calc beta2 * alpha2 * beta2⁻¹ = alpha2⁻¹ * (alpha2 * beta2 * alpha2) * beta2⁻¹ := by group
    _ = alpha2⁻¹ := by rw [alpha2_beta2_alpha2]; group

private theorem b2A_sq : b2A ^ 2 = a2A ^ 2 :=
  Subtype.ext (by
    rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, sq, sq]
    exact beta2_sq.trans alpha2_sq.symm)

private noncomputable def q8A : QuaternionGroup 2 →* ↥QA45.originalSubgroup :=
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift a2A_pow_four
    b2A_conj_a2A b2A_sq

private theorem q8A_a (k : ZMod (2 * 2)) : q8A (QuaternionGroup.a k) = a2A ^ k.val := rfl

private theorem q8A_xa (k : ZMod (2 * 2)) : q8A (QuaternionGroup.xa k) = b2A * a2A ^ k.val := rfl

private theorem q8A_a_two : q8A (QuaternionGroup.a 2) = tA := by
  rw [q8A_a]
  exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact (sq alpha2).trans alpha2_sq)

private theorem q8A_injective : Function.Injective q8A := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have h := CFSG.GroupTheory.quaternion_a_two_mem_of_ne_bot hne
  rw [MonoidHom.mem_ker, q8A_a_two] at h
  exact t_ne_one (congrArg Subtype.val h)

private theorem card_range_q8A : Nat.card q8A.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective q8A_injective).toEquiv, Nat.card_eq_fintype_card,
    QuaternionGroup.card]

private theorem range_q8A_le {P : Subgroup ↥QA45.originalSubgroup} (ha : a2A ∈ P) (hb : b2A ∈ P) :
    q8A.range ≤ P := by
  rintro _ ⟨q, rfl⟩
  rcases q with k | k
  · rw [q8A_a]
    exact P.pow_mem ha _
  · rw [q8A_xa]
    exact P.mul_mem hb (P.pow_mem ha _)

private theorem range_q8A_le_Pp : q8A.range ≤ Pp :=
  range_q8A_le (Subgroup.mem_subgroupOf.mpr alpha2_mem_Q) (Subgroup.mem_subgroupOf.mpr beta2_mem_Q)

private theorem range_q8A_le_centralizer :
    q8A.range ≤ Subgroup.centralizer ({s1A} : Set ↥QA45.originalSubgroup) :=
  range_q8A_le (cSigmaQA45_le_centralizer (Subgroup.subset_closure (by simp)))
    (cSigmaQA45_le_centralizer (Subgroup.subset_closure (by simp)))

private theorem eq_one_or_eq_tA_of_mem_range_q8A {x : ↥QA45.originalSubgroup}
    (hx : x ∈ q8A.range) (hx2 : x ^ 2 = 1) : x = 1 ∨ x = tA := by
  obtain ⟨q, rfl⟩ := hx
  have hq : q * q = 1 := q8A_injective (by rw [map_mul, ← sq, hx2, map_one])
  rcases q8_eq_one_or_eq_a_two hq with rfl | rfl
  · exact Or.inl (map_one q8A)
  · exact Or.inr q8A_a_two

theorem card_H_inf_centralizer_sigma1_mul_sigma2_inv (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (h3₂ : orderOf σ₂ = 3)
    (hc : Commute σ₁ σ₂) {y : ↥(H z)} (hy : orderOf y = 9) (hyσ : y ^ 3 = σ₁) :
    Nat.card ↥(H z ⊓ Subgroup.centralizer ({((σ₁ * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) =
      2 ^ 6 * 27 := by
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have hp1 : σ₁ ^ 3 = 1 := by rw [← h3₁]; exact pow_orderOf_eq_one σ₁
  have hp2 : σ₂ ^ 3 = 1 := by rw [← h3₂]; exact pow_orderOf_eq_one σ₂
  have hφs : φ (σ₁ * σ₂⁻¹) = s1A * s2A⁻¹ := by rw [map_mul, map_inv, hσ₁, hσ₂]
  have h3 : orderOf (σ₁ * σ₂⁻¹) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ fun h => s1A_mul_s2A_inv_ne_one ?_
    · rw [hc.inv_right.mul_pow, inv_pow, hp1, hp2, inv_one, one_mul]
    · rw [← hφs, h, map_one]
  have h4 := fixDimV_sigma1_mul_sigma2_inv_eq_four hJ hcard hcomm hCHJ φ hker hrange.ge hσ₁ hσ₂
    hy hyσ
  rw [card_H_inf_centralizer_eq hcard φ hker h3, card_CJ_eq_two_mul hJ hcard hcomm h3, h4, hφs,
    hrange, card_QP45_inf_centralizer_sigma1_mul_sigma2_inv]
  norm_num

theorem card_H_inf_centralizer_sigma1_mul_sigma2
    (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    Nat.card ↥(H z ⊓ Subgroup.centralizer ({((σ₁ * σ₂ : ↥(H z)) : G)} : Set G)) =
      2 ^ 3 * 27 := by
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have h3₂ : orderOf σ₂ = 3 := by
    rw [← hu, ← MulAut.conj_apply, MulEquiv.orderOf_eq, h3₁]
  obtain ⟨h3, h0⟩ := fixDimV_sigma1_mul_sigma2_eq_zero hJ hcard hcomm hCHJ φ hker hrange.ge hσ₁
    hσ₂ h3₂ hc hne hy hyσ hu
  have hφs : φ (σ₁ * σ₂) = s1A * s2A := by rw [map_mul, hσ₁, hσ₂]
  rw [card_H_inf_centralizer_eq hcard φ hker h3, card_CJ_eq_two_mul hJ hcard hcomm h3, h0, hφs,
    hrange, card_QP45_inf_centralizer_sigma1_mul_sigma2]
  norm_num

theorem card_le_of_le_H_inf_centralizer_sigma1_mul_sigma2
    (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hrange : φ.range = QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hσ₂ : φ σ₂ = s2A) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) {S : Subgroup G}
    (hS : S ≤ H z ⊓ Subgroup.centralizer ({((σ₁ * σ₂ : ↥(H z)) : G)} : Set G))
    (hS2 : IsPGroup 2 S) : Nat.card S ≤ 8 :=
  (card_le_of_isPGroup_two hS hS2
    (card_H_inf_centralizer_sigma1_mul_sigma2 hJ hcard hcomm hCHJ φ hker hrange hσ₁ hσ₂ hc hne
      hy hyσ hu) ⟨13, rfl⟩).trans_eq (by norm_num)

private theorem map_centralizer_inf_comap_range_q8A (hcard : Nat.card (J z) = 2 ^ 9)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (h3₁ : orderOf σ₁ = 3) :
    (Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓ q8A.range.comap φ).map φ = q8A.range := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr inf_le_right
  · intro q hq
    have hq' : q ∈ (Subgroup.centralizer ({σ₁} : Set ↥(H z))).map φ := by
      rw [map_centralizer_eq_of_orderOf_eq_three hcard φ hker h3₁, hσ₁]
      exact ⟨hQP (range_q8A_le_Pp hq), range_q8A_le_centralizer hq⟩
    obtain ⟨c, hcC, rfl⟩ := hq'
    exact ⟨c, ⟨hcC, hq⟩, rfl⟩

private theorem card_centralizer_inf_comap_range_q8A (hcard : Nat.card (J z) = 2 ^ 9)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range) {σ₁ : ↥(H z)}
    (hσ₁ : φ σ₁ = s1A) (h3₁ : orderOf σ₁ = 3) :
    Nat.card ↥(Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓ q8A.range.comap φ) =
      Nat.card ↥(CJ z (σ₁ : G)) * 8 := by
  have hker' : φ.ker ⊓ (Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓ q8A.range.comap φ) =
      φ.ker ⊓ Subgroup.centralizer ({σ₁} : Set ↥(H z)) := by
    refine le_antisymm (inf_le_inf_left _ inf_le_left) fun c hc => ?_
    obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hcK, Subgroup.mem_inf.mpr ⟨hcC, ?_⟩⟩
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hcK]
    exact one_mem _
  rw [card_eq_card_ker_inf_mul_card_map φ
      (Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓ q8A.range.comap φ), hker',
    map_centralizer_inf_comap_range_q8A hcard φ hker hQP hσ₁ h3₁, card_range_q8A,
    ← map_ker_inf_centralizer_eq_CJ φ hker σ₁,
    Subgroup.card_map_of_injective (H z).subtype_injective]

private theorem card_le_four_of_le_preimage (φ : ↥(H z) →* ↥QA45.originalSubgroup)
    (hker : φ.ker = (J z).subgroupOf (H z)) {σ₁ : ↥(H z)}
    (ε : ↥(CJ z (σ₁ : G)) ≃* QuaternionGroup 2) {E : Subgroup G}
    (hE : E ≤ (Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓ q8A.range.comap φ).map (H z).subtype)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  have hEH : E ≤ H z := hE.trans (Subgroup.map_subtype_le _)
  have hcardE : Nat.card E = Nat.card (E.subgroupOf (H z)) := by
    have h := Subgroup.card_map_of_injective (K := E.subgroupOf (H z)) (H z).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEH] at h
    exact h
  have hmemC : ∀ e ∈ E.subgroupOf (H z), e ∈ Subgroup.centralizer ({σ₁} : Set ↥(H z)) ∧
      φ e ∈ q8A.range := by
    intro e he
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp (hE (Subgroup.mem_subgroupOf.mp he))
    rw [show c = e from Subtype.ext hce] at hc
    obtain ⟨hcC, hcQ⟩ := Subgroup.mem_inf.mp hc
    exact ⟨hcC, Subgroup.mem_comap.mp hcQ⟩
  have hsq : ∀ e ∈ E.subgroupOf (H z), e ^ 2 = 1 := fun e he =>
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hE2 _ (Subgroup.mem_subgroupOf.mp he))
  have himage : Nat.card ↥((E.subgroupOf (H z)).map φ) ≤ 2 := by
    refine card_le_two_of_forall_eq_one_or_eq (c := tA) (Subtype.ext t_sq) fun x hx => ?_
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    exact eq_one_or_eq_tA_of_mem_range_q8A (hmemC e he).2 (by rw [← map_pow, hsq e he, map_one])
  have hkernel : Nat.card ↥(φ.ker ⊓ E.subgroupOf (H z)) ≤ 2 := by
    rw [← Subgroup.card_map_of_injective (H z).subtype_injective]
    have hc₀ : ((ε.symm (QuaternionGroup.a 2) : ↥(CJ z (σ₁ : G))) : G) *
        ((ε.symm (QuaternionGroup.a 2) : ↥(CJ z (σ₁ : G))) : G) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul,
        show QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) by decide,
        map_one, Subgroup.coe_one]
    refine card_le_two_of_forall_eq_one_or_eq hc₀ fun x hx => ?_
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨heK, heE⟩ := Subgroup.mem_inf.mp he
    rw [hker] at heK
    have hw : (e : G) ∈ CJ z (σ₁ : G) :=
      mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hmemC e heE).1)),
        Subgroup.mem_subgroupOf.mp heK⟩
    have hw2 : (⟨(e : G), hw⟩ : ↥(CJ z (σ₁ : G))) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hE2 _ (Subgroup.mem_subgroupOf.mp heE))
    have hεw : ε ⟨(e : G), hw⟩ * ε ⟨(e : G), hw⟩ = 1 := by rw [← map_mul, ← sq, hw2, map_one]
    rcases q8_eq_one_or_eq_a_two hεw with h | h
    · exact Or.inl (congrArg Subtype.val ((MulEquiv.map_eq_one_iff ε).mp h))
    · exact Or.inr (congrArg Subtype.val ((MulEquiv.eq_symm_apply ε).mpr h))
  rw [hcardE, card_eq_card_ker_inf_mul_card_map φ (E.subgroupOf (H z))]
  exact (Nat.mul_le_mul hkernel himage).trans (by norm_num)

theorem exists_le_H_inf_centralizer_sigma1_card_eq_sixtyFour (hJ : IsExtraspecial2 (J z))
    (hcard : Nat.card (J z) = 2 ^ 9) (hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCHJ : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z)
    (φ : ↥(H z) →* ↥QA45.originalSubgroup) (hker : φ.ker = (J z).subgroupOf (H z))
    (hQP : QP45.originalSubgroup.subgroupOf QA45.originalSubgroup ≤ φ.range)
    {σ₁ σ₂ : ↥(H z)} (hσ₁ : φ σ₁ = s1A) (hc : Commute σ₁ σ₂)
    (hne : CJ z (σ₁ : G) ≠ CJ z (σ₂ : G)) {y u : ↥(H z)} (hy : orderOf y = 9)
    (hyσ : y ^ 3 = σ₁) (hu : u * σ₁ * u⁻¹ = σ₂) :
    ∃ T₁ : Subgroup G, T₁ ≤ H z ⊓ Subgroup.centralizer ({(σ₁ : G)} : Set G) ∧ IsPGroup 2 T₁ ∧
      Nat.card T₁ = 64 ∧
      ∀ E : Subgroup G, E ≤ T₁ → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  have h3₁ : orderOf σ₁ = 3 := by
    rw [← hyσ, orderOf_pow_of_dvd (x := y) (n := 3) (by norm_num) (by rw [hy]; norm_num), hy]
  have h3₂ : orderOf σ₂ = 3 := by
    rw [← hu, ← MulAut.conj_apply, MulEquiv.orderOf_eq, h3₁]
  have h8₁ : Nat.card (CJ z (σ₁ : G)) = 8 := card_CJ_eq_eight_of_cube hJ hcard hcomm hCHJ hy hyσ
  have h8₂ : Nat.card (CJ z (σ₂ : G)) = 8 := by
    rw [← hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, card_CJ_conj_eq, h8₁]
  obtain ⟨⟨ε⟩, -⟩ := nonempty_CJ_mulEquiv_quaternion hJ hcomm h3₁ h3₂ hc h8₁ h8₂ hne
  have hcardT : Nat.card ↥((Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓
      q8A.range.comap φ).map (H z).subtype) = 64 := by
    rw [Subgroup.card_map_of_injective (H z).subtype_injective,
      card_centralizer_inf_comap_range_q8A hcard φ hker hQP hσ₁ h3₁, h8₁]
  refine ⟨(Subgroup.centralizer ({σ₁} : Set ↥(H z)) ⊓ q8A.range.comap φ).map (H z).subtype, ?_,
    IsPGroup.of_card (n := 6) (hcardT.trans (by norm_num)), hcardT,
    fun E hE hEa => card_le_four_of_le_preimage φ hker ε hE hEa.2⟩
  intro g hg
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg
  exact Subgroup.mem_inf.mpr ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1))⟩

end Model

end CFSG.RankThree.GF2n.Parrott.Remarks
