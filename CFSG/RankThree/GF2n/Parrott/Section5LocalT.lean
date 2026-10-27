module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalSigma
public import CFSG.RankThree.GF2n.Parrott.Section5Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem conjZ_sigma2_eq_one_of_qH_map (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z σ₂ = 1 :=
  conjZ_eq_one_of_mem_Q (z := z) D h σ₂
    (Subgroup.mem_subgroupOf.mpr (by rw [hq₂]; exact sigma2_mem_Q))

private theorem conjZ_mul_sigma2_inv_eq_one_of_qH_map (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  rw [map_mul, map_inv, conjZ_sigma1Nine h D, conjZ_sigma2_eq_one_of_qH_map (z := z) D h hq₂,
    inv_one, mul_one]

private theorem conjZ_mul_sigma2_eq_one_of_qH_map (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    conjZ z (sigma1Nine (z := z) D * σ₂) = 1 := by
  rw [map_mul, conjZ_sigma1Nine h D, conjZ_sigma2_eq_one_of_qH_map (z := z) D h hq₂, mul_one]

theorem mem_centralizer_z1_iff_qH_mem_QP45 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (x : ↥(H z)) :
    (x : G) ∈ centralizer ({z₁} : Set G) ↔
      qH (z := z) D x ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  classical
  set K : Subgroup ↥(H z) :=
    (H z ⊓ Subgroup.centralizer ({z₁} : Set G)).subgroupOf (H z) with hK
  have hPK : P_H D ≤ K := by
    intro y hy
    rw [hK, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    have hyZ : conjZ z y = 1 :=
      conjZ_eq_one_of_mem_Q (z := z) D h y ((mem_P_H_iff D y).mp hy)
    have hcent := centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := y) hyZ
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hcent hz₁)).symm
  have hKne : K ≠ ⊤ := by
    intro htop
    obtain ⟨x₀, hx₀H, hx₀C⟩ := exists_mem_H_not_mem_centralizer_z1 h hZ hz₁ hz₁z hord
    have hx₀K : (⟨x₀, hx₀H⟩ : ↥(H z)) ∈ K := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [hK, Subgroup.mem_subgroupOf] at hx₀K
    exact hx₀C hx₀K.2
  have hdvd : K.index ∣ 2 := by
    have h := Subgroup.index_dvd_of_le hPK
    rwa [index_P_H] at h
  have hKindex : K.index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (Subgroup.index_eq_one.mp h1) hKne
    · exact h1
  have hPK_eq : P_H D = K := by
    refine Subgroup.eq_of_le_of_card_ge hPK ?_
    have h1 := Subgroup.card_mul_index (P_H D)
    have h2 := Subgroup.card_mul_index K
    rw [index_P_H] at h1; rw [hKindex] at h2
    omega
  constructor
  · intro hx
    have hxK : x ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr ⟨x.2, hx⟩
    rw [← hPK_eq] at hxK
    exact (mem_P_H_iff D x).mp hxK
  · intro hx
    have hxK : x ∈ K := by
      rw [← hPK_eq]
      exact (mem_P_H_iff D x).mpr hx
    rw [hK, Subgroup.mem_subgroupOf] at hxK
    exact hxK.2

theorem centerIn_J_le_of_isSylowOf_centralizer (h : Tim79a.ParrottHyp z) {y : ↥(H z)}
    (hy : conjZ z y = 1) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(y : G)} : Set G))) :
    centerIn (J z) ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := H z ⊓ centralizer ({(y : G)} : Set G) with hK
  have hZK : centerIn (J z) ≤ K := by
    intro e he
    exact Subgroup.mem_inf.mpr ⟨centerIn_le_H z he,
      centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := y) hy he⟩
  have hnorm : K ≤ Subgroup.normalizer ((centerIn (J z) : Subgroup G) : Set G) := by
    refine le_trans inf_le_left ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (centerIn_le_H (z := z))).mp
      (centerIn_subgroupOf_normal z)
  have hZ2 : IsPGroup 2 (centerIn (J z)) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [card_centerIn_J h]
    norm_num
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  haveI : ((centerIn (J z)).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZK).mpr hnorm
  have hZ2' : IsPGroup 2 ↥((centerIn (J z)).subgroupOf K) := by
    have hc := hZ2.comap_subtype (K := K)
    rwa [Subgroup.comap_subtype] at hc
  have hle : (centerIn (J z)).subgroupOf K ≤ (Q : Subgroup ↥K) :=
    IsPGroup.le_sylow_of_normal hZ2' Q
  intro e he
  have heK : e ∈ K := hZK he
  have heQ : (⟨e, heK⟩ : ↥K) ∈ (Q : Subgroup ↥K) := hle (Subgroup.mem_subgroupOf.mpr he)
  rw [hQ] at heQ
  exact heQ

private theorem exists_mem_centralizer_pow_of_mem_centralizer (h : Tim79a.ParrottHyp z)
    {y : ↥(H z)} (hy : orderOf y = 3)
    {a : QA45.originalSubgroup}
    (ha : a ∈ Subgroup.centralizer ({qH (z := z) D y} : Set QA45.originalSubgroup))
    (ha2 : a * a = 1) :
    ∃ b : ↥(H z), b ∈ Subgroup.centralizer ({y} : Set ↥(H z)) ∧ qH D b = a ∧
      (b : G) ^ (2 ^ 11) = 1 := by
  classical
  have hamap : a ∈ (Subgroup.centralizer ({y} : Set ↥(H z))).map (qH D) := by
    rw [map_centralizer_qH_of_orderOf_three D y hy]
    exact ha
  obtain ⟨b, hbC, hqb⟩ := Subgroup.mem_map.mp hamap
  refine ⟨b, hbC, hqb, ?_⟩
  have hbbq : qH D (b * b) = 1 := by
    rw [map_mul, hqb, ha2]
  have hbbJ : b * b ∈ (J z).subgroupOf (H z) := (J_mem_iff D (b * b)).mpr hbbq
  have hbbG : (b : G) * (b : G) ∈ J z := by
    simpa using Subgroup.mem_subgroupOf.mp hbbJ
  have h1 : (⟨(b : G) * (b : G), hbbG⟩ : ↥(J z)) ^ Nat.card (J z) = 1 := pow_card_eq_one'
  have h2 : ((b : G) * (b : G)) ^ (2 ^ 10) = 1 := by
    rw [card_J h] at h1
    simpa using congrArg Subtype.val h1
  calc (b : G) ^ (2 ^ 11) = (b : G) ^ (2 * 2 ^ 10) := by
        rw [show (2 : ℕ) ^ 11 = 2 * 2 ^ 10 by norm_num]
    _ = ((b : G) ^ 2) ^ (2 ^ 10) := pow_mul _ _ _
    _ = ((b : G) * (b : G)) ^ (2 ^ 10) := by rw [pow_two]
    _ = 1 := h2

private theorem exists_mem_isSylowOf_conj_of_pow {y : ↥(H z)} {b : ↥(H z)}
    (hbC : b ∈ Subgroup.centralizer ({y} : Set ↥(H z)))
    (hbpow : (b : G) ^ (2 ^ 11) = 1) {a : QA45.originalSubgroup} (hqb : qH D b = a)
    (haP : a ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(y : G)} : Set G))) :
    ∃ xH : ↥(H z), (xH : G) ∈ T ∧
      qH D xH ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup G := H z ⊓ centralizer ({(y : G)} : Set G) with hK
  have hbK : (b : G) ∈ K := by
    refine Subgroup.mem_inf.mpr ⟨b.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hbC)
  let bK : ↥K := ⟨(b : G), hbK⟩
  have hbKord : orderOf bK ∣ 2 ^ 11 := by
    have h : orderOf (b : G) ∣ 2 ^ 11 := orderOf_dvd_of_pow_eq_one hbpow
    have h2 : orderOf bK = orderOf (b : G) := by
      rw [← Subgroup.orderOf_coe bK]
    rwa [h2]
  have hB2 : IsPGroup 2 (Subgroup.zpowers bK) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    refine ⟨11, ?_⟩
    have h1 : orderOf g = orderOf (g : ↥K) :=
      (Subgroup.orderOf_coe (H := Subgroup.zpowers bK) g).symm
    rw [h1]
    exact (orderOf_dvd_of_mem_zpowers g.2).trans hbKord
  obtain ⟨Q, hQle⟩ := hB2.exists_le_sylow
  let T' : Subgroup G := (Q : Subgroup ↥K).map K.subtype
  have hT' : IsSylowOf 2 T' K := ⟨Q, rfl⟩
  have hbT' : (b : G) ∈ T' := by
    refine Subgroup.mem_map.mpr ⟨bK, ?_, rfl⟩
    exact hQle (Subgroup.mem_zpowers bK)
  obtain ⟨c, hcK, hc⟩ := hT.exists_mem_conj hT'
  have hmem : c⁻¹ * (b : G) * c ∈ T := (hc (b : G)).mp hbT'
  let cH : ↥(H z) := ⟨(c : G), hcK.1⟩
  let xH : ↥(H z) := cH⁻¹ * b * cH
  have hxT : (xH : G) ∈ T := hmem
  refine ⟨xH, hxT, ?_⟩
  have hqx : qH D xH = (qH D cH)⁻¹ * a * (qH D cH) := by
    simp only [xH, map_mul, map_inv, hqb]
  intro hmemP
  rw [hqx] at hmemP
  exact haP (by
    have h := (Subgroup.normal_of_index_eq_two index_QP45).conj_mem
      ((qH D cH)⁻¹ * a * (qH D cH)) hmemP (qH D cH)
    simpa [mul_assoc] using h)

theorem exists_mem_isSylowOf_conj_z1_of_not_mem_QP45 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {y : ↥(H z)}
    (hy : orderOf y = 3) {a : QA45.originalSubgroup}
    (ha : a ∈ centralizer ({qH (z := z) D y} : Set QA45.originalSubgroup)) (ha2 : a * a = 1)
    (haP : a ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) {T : Subgroup G}
    (hT : IsSylowOf 2 T (H z ⊓ centralizer ({(y : G)} : Set G))) :
    ∃ x ∈ T, x * z₁ * x⁻¹ = z * z₁ := by
  obtain ⟨b, hbC, hqb, hbpow⟩ :=
    exists_mem_centralizer_pow_of_mem_centralizer (z := z) D h hy ha ha2
  obtain ⟨xH, hxT, hqxP⟩ :=
    exists_mem_isSylowOf_conj_of_pow (z := z) D hbC hbpow hqb haP hT
  have hxnotC : (xH : G) ∉ Subgroup.centralizer ({z₁} : Set G) := fun hmemC =>
    hqxP ((mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord xH).mp hmemC)
  exact ⟨(xH : G), hxT,
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord xH.2 hxnotC⟩

private noncomputable def centralizerSigma1QA45 : Subgroup QA45.originalSubgroup :=
  Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} :
    Set QA45.originalSubgroup)

private theorem mem_QP45_of_isPGroup_zpowers_centralizer_sigma1Nine
    (u : ↥(centralizerSigma1QA45)) (hu2 : IsPGroup 2 (Subgroup.zpowers u)) :
    (u : QA45.originalSubgroup) ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup QA45.originalSubgroup :=
    Subgroup.closure ({(⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup),
      (⟨beta2, beta2_mem_A⟩ : QA45.originalSubgroup)} : Set QA45.originalSubgroup) with hA
  obtain ⟨hq8, -, -⟩ := qa45_sigma_centralizer_sylow
  have hAle : A ≤ centralizerSigma1QA45 := by
    simpa [hA, centralizerSigma1QA45] using hq8.1
  have hAcard : Nat.card A = 8 := by simpa [hA] using hq8.2.1
  have hScard : Nat.card (centralizerSigma1QA45) = 648 := card_centralizer_sigma1_QA45
  have hAsylow : IsSylowOf 2 A centralizerSigma1QA45 := by
    refine isSylowOf_of_card hAle ?_
    rw [hAcard, hScard]
    have h648 : Nat.factorization 648 2 = 3 := by
      have hfac : 648 = 2 ^ 3 * 81 := by norm_num
      rw [hfac, Nat.factorization_mul (a := (2 : ℕ) ^ 3) (b := 81)
        (by norm_num) (by norm_num)]
      change ((2 : ℕ) ^ 3).factorization 2 + (81 : ℕ).factorization 2 = 3
      rw [Nat.factorization_pow_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (81 : ℕ)), add_zero]
    rw [h648]
    norm_num
  obtain ⟨Q, hQle⟩ := hu2.exists_le_sylow
  let T' : Subgroup QA45.originalSubgroup :=
    (Q : Subgroup ↥(centralizerSigma1QA45)).map (centralizerSigma1QA45).subtype
  have hT' : IsSylowOf 2 T' centralizerSigma1QA45 := ⟨Q, rfl⟩
  have huT' : (u : QA45.originalSubgroup) ∈ T' := by
    refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
    exact hQle (Subgroup.mem_zpowers u)
  obtain ⟨c, -, hc⟩ := hAsylow.exists_mem_conj hT'
  have hcA : c⁻¹ * (u : QA45.originalSubgroup) * c ∈ A :=
    (hc (u : QA45.originalSubgroup)).mp huT'
  have hAP : A ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact alpha2_mem_Q
    · exact beta2_mem_Q
  have hcP : c⁻¹ * (u : QA45.originalSubgroup) * c ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := hAP hcA
  have h := (Subgroup.normal_of_index_eq_two index_QP45).conj_mem
    (c⁻¹ * (u : QA45.originalSubgroup) * c) hcP c
  simpa [mul_assoc] using h

private theorem qH_mem_QP45_of_mem_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    {x : ↥(H z)} (hxT : (x : G) ∈ T₁) :
    qH (z := z) D x ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  classical
  have hxK : (x : G) ∈ H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} :
      Set G) := hT₁.le hxT
  have hxS : qH D x ∈ centralizerSigma1QA45 := by
    have hxmem : x ∈ Subgroup.centralizer ({sigma1Nine (z := z) D} : Set ↥(H z)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxK.2)
    have hmap : qH D x ∈ (Subgroup.centralizer ({sigma1Nine (z := z) D} :
        Set ↥(H z))).map (qH D) := Subgroup.mem_map.mpr ⟨x, hxmem, rfl⟩
    rwa [map_centralizer_sigma1Nine_eq D h] at hmap
  let u : ↥(centralizerSigma1QA45) := ⟨qH D x, hxS⟩
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    obtain ⟨k, hk⟩ := hT₁.isPGroup.exists_orderOf_dvd_pow (⟨(x : G), hxT⟩ : ↥T₁)
    have hk' : orderOf x ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe (⟨(x : G), hxT⟩ : ↥T₁)] at hk
      rwa [Subgroup.orderOf_coe x] at hk
    have hux : orderOf u ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe u]
      exact (orderOf_map_dvd (qH D) x).trans hk'
    refine ⟨k, ?_⟩
    have h1 : orderOf g = orderOf (g : ↥(centralizerSigma1QA45)) :=
      (Subgroup.orderOf_coe (H := Subgroup.zpowers u) g).symm
    rw [h1]
    exact (orderOf_dvd_of_mem_zpowers g.2).trans hux
  exact mem_QP45_of_isPGroup_zpowers_centralizer_sigma1Nine u hu2

theorem centerIn_J_le_centerIn_of_isSylowOf_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z)
    {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    centerIn (J z) ≤ centerIn T₁ := by
  have hZT : centerIn (J z) ≤ T₁ :=
    centerIn_J_le_of_isSylowOf_centralizer h (conjZ_sigma1Nine h D) hT₁
  intro e he
  refine Subgroup.mem_inf.mpr ⟨hZT he, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hxT
  have hxH : (x : G) ∈ H z := (hT₁.le hxT).1
  let xH : ↥(H z) := ⟨x, hxH⟩
  have hqx : qH D xH ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    qH_mem_QP45_of_mem_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁ (x := xH) hxT
  have hconj : conjZ z xH = 1 := conjZ_eq_one_of_mem_Q (z := z) D h xH hqx
  have hcent := centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := xH) hconj
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent he)).symm

theorem exists_mem_isSylowOf_centralizer_sigma1Nine_mul_inv_conj_z1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    ∃ x ∈ T₂, x * z₁ * x⁻¹ = z * z₁ := by
  let s1A : QA45.originalSubgroup := ⟨sigma1, sigma1_mem_A⟩
  let s2A : QA45.originalSubgroup := ⟨sigma2, sigma2_mem_A⟩
  let uA : QA45.originalSubgroup := ⟨u, u_mem_A⟩
  let vA : QA45.originalSubgroup := ⟨v, v_mem_A⟩
  have hy : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂⁻¹)]
    exact orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
  have hqy : qH D (sigma1Nine (z := z) D * σ₂⁻¹) = s1A * s2A⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hu : uA * vA ∈ Subgroup.centralizer ({(s1A * s2A⁻¹)} :
      Set QA45.originalSubgroup) := by
    obtain ⟨-, he4, -⟩ := qa45_sigma_centralizer_sylow
    exact he4.1 (Subgroup.subset_closure (by simp [uA, vA]))
  have ha : uA * vA ∈ Subgroup.centralizer ({(qH D (sigma1Nine (z := z) D * σ₂⁻¹))} :
      Set QA45.originalSubgroup) := by
    rwa [hqy]
  have ha2 : (uA * vA) * (uA * vA) = 1 := by
    have hu2 : uA * uA = 1 := Subtype.ext u_sq
    have hv2 : vA * vA = 1 := Subtype.ext v_sq
    have huv : Commute uA vA := Subtype.ext Certificates.certificate946005.u_commute_v
    rw [Commute.mul_mul_mul_comm huv.symm uA vA, hu2, hv2, one_mul]
  have haP : uA * vA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    intro hmem
    have huP : uA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := u_mem_Q
    have hvP : vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      have h1 : uA⁻¹ * (uA * vA) ∈
          QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ huP) hmem
      rwa [inv_mul_cancel_left] at h1
    exact v_not_mem_Q hvP
  exact exists_mem_isSylowOf_conj_z1_of_not_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord
    (y := sigma1Nine (z := z) D * σ₂⁻¹) hy (a := uA * vA) ha ha2 haP hT₂

theorem exists_mem_isSylowOf_centralizer_sigma1Nine_mul_conj_z1 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₃ : Subgroup G}
    (hT₃ : IsSylowOf 2 T₃
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))) :
    ∃ x ∈ T₃, x * z₁ * x⁻¹ = z * z₁ := by
  let s1A : QA45.originalSubgroup := ⟨sigma1, sigma1_mem_A⟩
  let s2A : QA45.originalSubgroup := ⟨sigma2, sigma2_mem_A⟩
  let vA : QA45.originalSubgroup := ⟨v, v_mem_A⟩
  let bA : QA45.originalSubgroup := ⟨beta, beta_mem_A⟩
  have hy : orderOf (sigma1Nine (z := z) D * σ₂) = 3 := by
    rw [← Subgroup.orderOf_coe (sigma1Nine (z := z) D * σ₂)]
    exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  have hqy : qH D (sigma1Nine (z := z) D * σ₂) = s1A * s2A := by
    rw [map_mul, qH_sigma1Nine, hq₂]
  have hw : vA * bA ∈ Subgroup.centralizer ({(s1A * s2A)} :
      Set QA45.originalSubgroup) := by
    obtain ⟨-, -, hd8⟩ := qa45_sigma_centralizer_sylow
    exact hd8.1 (Subgroup.subset_closure (by simp [vA, bA]))
  have ha : vA * bA ∈ Subgroup.centralizer ({(qH D (sigma1Nine (z := z) D * σ₂))} :
      Set QA45.originalSubgroup) := by
    rwa [hqy]
  have ha2 : (vA * bA) * (vA * bA) = 1 := Subtype.ext qa45L1Facts.vbeta_sq
  have haP : vA * bA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    intro hmem
    have hbP : bA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := beta_mem_Q
    have hvP : vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      have h1 : (vA * bA) * bA⁻¹ ∈
          QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
        Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hbP)
      rwa [mul_inv_cancel_right] at h1
    exact v_not_mem_Q hvP
  exact exists_mem_isSylowOf_conj_z1_of_not_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord
    (y := sigma1Nine (z := z) D * σ₂) hy (a := vA * bA) ha ha2 haP hT₃

theorem z_mem_commutator_of_isSylowOf_centralizer_sigma1Nine_mul (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₃ : Subgroup G}
    (hT₃ : IsSylowOf 2 T₃
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G))) :
    z ∈ ⁅T₃, T₃⁆ := by
  obtain ⟨z₁, hz₁sup, hz₁z, hord⟩ := exists_z1 (z := z) h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hz₁sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  have hZy : conjZ z (sigma1Nine (z := z) D * σ₂) = 1 :=
    conjZ_mul_sigma2_eq_one_of_qH_map (z := z) D h hq₂
  have hZT : centerIn (J z) ≤ T₃ :=
    centerIn_J_le_of_isSylowOf_centralizer h hZy hT₃
  have hzT : z ∈ T₃ := hZT (z_mem_centerIn_J h)
  have hz₁T : z₁ ∈ T₃ := hZT hz₁
  obtain ⟨x, hxT, hxconj⟩ :=
    exists_mem_isSylowOf_centralizer_sigma1Nine_mul_conj_z1 (z := z) D h hZ hz₁ hz₁z hord
      hσ₂ hq₂ hc₂ hT₃
  have hcomm : ⁅x, z₁⁆ = z := by
    rw [commutatorElement_def, hxconj, mul_assoc, mul_inv_cancel, mul_one]
  have hmem := Subgroup.commutator_mem_commutator (H₁ := T₃) (H₂ := T₃) hxT hz₁T
  rwa [hcomm] at hmem

private theorem not_mem_centerIn_of_conj_z1 (h : Tim79a.ParrottHyp z) {z₁ x : G}
    {T₂ : Subgroup G} (hzcent : z ∈ centerIn T₂) (hxT : x ∈ T₂)
    (hxconj : x * z₁ * x⁻¹ = z * z₁) :
    z₁ ∉ centerIn T₂ ∧ z * z₁ ∉ centerIn T₂ := by
  have hzne1 : z ≠ 1 := by
    intro hz1
    have hordz : orderOf z = 2 := h.1
    rw [hz1, orderOf_one] at hordz
    exact absurd hordz (by norm_num)
  have hxzx : x * z * x⁻¹ = z := by
    have hcomm : x * z = z * x :=
      Subgroup.mem_centralizer_iff.mp hzcent.2 x hxT
    rw [hcomm, mul_inv_cancel_right]
  constructor
  · intro hmem
    have hxcomm : x * z₁ = z₁ * x := Subgroup.mem_centralizer_iff.mp hmem.2 x hxT
    have hxz : x * z₁ * x⁻¹ = z₁ := by rw [hxcomm, mul_inv_cancel_right]
    have hzne : z * z₁ ≠ z₁ := by
      intro heq
      apply hzne1
      have h := congrArg (fun t => t * z₁⁻¹) heq
      simpa [mul_assoc] using h
    exact hzne (hxconj.symm.trans hxz)
  · intro hmem
    have hxcomm : x * (z * z₁) = (z * z₁) * x :=
      Subgroup.mem_centralizer_iff.mp hmem.2 x hxT
    have hxz : x * (z * z₁) * x⁻¹ = z₁ := by
      calc x * (z * z₁) * x⁻¹ = (x * z * x⁻¹) * (x * z₁ * x⁻¹) := by group
        _ = z * (z * z₁) := by rw [hxzx, hxconj]
        _ = z₁ := by
            have hzsq : z * z = 1 := by
              have h2 := pow_orderOf_eq_one z
              rwa [h.1, pow_two] at h2
            rw [← mul_assoc, hzsq, one_mul]
    have heq : z * z₁ = z₁ := by
      calc z * z₁ = (z * z₁) * x * x⁻¹ := by rw [mul_inv_cancel_right]
        _ = x * (z * z₁) * x⁻¹ := by rw [hxcomm]
        _ = z₁ := hxz
    have : z = 1 := by
      have h := congrArg (fun t => t * z₁⁻¹) heq
      simpa [mul_assoc] using h
    exact hzne1 this

theorem centerIn_inf_centerIn_J_eq_zpowers_of_isSylowOf_centralizer_sigma1Nine_mul_inv
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {T₂ : Subgroup G}
    (hT₂ : IsSylowOf 2 T₂
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) :
    centerIn T₂ ⊓ centerIn (J z) = Subgroup.zpowers z := by
  obtain ⟨z₁, hz₁sup, hz₁z, hord⟩ := exists_z1 (z := z) h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hz₁sup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z₁)
  have hZy : conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 :=
    conjZ_mul_sigma2_inv_eq_one_of_qH_map (z := z) D h hq₂
  have hZT : centerIn (J z) ≤ T₂ :=
    centerIn_J_le_of_isSylowOf_centralizer h hZy hT₂
  have hzT : z ∈ T₂ := hZT (z_mem_centerIn_J h)
  have hzCT : z ∈ Subgroup.centralizer (T₂ : Set G) :=
    Subgroup.centralizer_le (le_trans hT₂.le inf_le_left) (z_centralizes_H h)
  have hzcent : z ∈ centerIn T₂ := ⟨hzT, hzCT⟩
  obtain ⟨x, hxT, hxconj⟩ :=
    exists_mem_isSylowOf_centralizer_sigma1Nine_mul_inv_conj_z1 (z := z) D h hZ hz₁ hz₁z hord
      hσ₂ hq₂ hc₂ hT₂
  obtain ⟨hz1_not, hzz1_not⟩ := not_mem_centerIn_of_conj_z1 h hzcent hxT hxconj
  refine le_antisymm ?_ ?_
  · intro e he
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he.2 with h1 | h1 | h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers z
    · exact absurd (h1 ▸ he.1) hz1_not
    · exact absurd (h1 ▸ he.1) hzz1_not
  · rw [Subgroup.zpowers_le]
    exact ⟨hzcent, z_mem_centerIn_J h⟩

end CFSG.RankThree.GF2n.Parrott
