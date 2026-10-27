module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalW
public import CFSG.RankThree.GF2n.Parrott.Section5LocalSpin
public import CFSG.RankThree.GF2n.Parrott.Section5SigmaThree
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42ClassVSpin

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G]

private theorem inv_mod_w_props {N : Subgroup G} (hN : IsPGroup 2 N) {x ρ : G}
    (hx : x * x = 1) (hρ : orderOf ρ = 3)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hinv : x * ρ * x⁻¹ * ρ ∈ N) :
    ∃ w : G, w = x * ρ * x⁻¹ * ρ⁻¹ ∧ x * w * x⁻¹ = w⁻¹ ∧
      w * ρ⁻¹ = x * ρ * x⁻¹ * ρ ∧ w ^ 3 ∈ N := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hρ3 : ρ ^ 3 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hρ3' : ρ * ρ * ρ = 1 := by rw [← pow_three', hρ3]
  have hρinv2 : ρ⁻¹ * ρ⁻¹ = ρ := by
    have h : ρ ^ (-2 : ℤ) = ρ := by
      have h := zpow_eq_zpow_emod' (-2) hρ3
      norm_num at h
      simpa using h
    simpa [zpow_neg, pow_two, mul_inv_rev] using h
  let w : G := x * ρ * x⁻¹ * ρ⁻¹
  have hwconj : x * w * x⁻¹ = w⁻¹ := by
    unfold w
    rw [hxinv]
    calc x * (x * ρ * x * ρ⁻¹) * x
        = (x * x) * ρ * x * ρ⁻¹ * x := by group
      _ = ρ * x * ρ⁻¹ * x := by rw [hx, one_mul]
      _ = ρ * x⁻¹ * ρ⁻¹ * x⁻¹ := by rw [hxinv]
      _ = (x * ρ * x * ρ⁻¹)⁻¹ := by group
  have hwρ : w * ρ⁻¹ = x * ρ * x⁻¹ * ρ := by
    unfold w
    calc (x * ρ * x⁻¹ * ρ⁻¹) * ρ⁻¹ = x * ρ * x⁻¹ * (ρ⁻¹ * ρ⁻¹) := by group
      _ = x * ρ * x⁻¹ * ρ := by rw [hρinv2]
  have hw_heq : w = (x * ρ * x⁻¹ * ρ) * ρ := by
    rw [← hwρ]
    group
  have hw3 : w ^ 3 ∈ N := by
    set n : G := x * ρ * x⁻¹ * ρ with hn
    have hnN : n ∈ N := hinv
    have hn1 : ρ * n * ρ⁻¹ ∈ N := hρN n hnN
    have hn2 : ρ * ρ * n * (ρ * ρ)⁻¹ ∈ N := by
      have h := hρN (ρ * n * ρ⁻¹) hn1
      convert h using 1
      group
    have h := hw_heq
    rw [h] at *
    clear h
    have hw3eq : (n * ρ) ^ 3 =
        n * (ρ * n * ρ⁻¹) * (ρ * ρ * n * (ρ * ρ)⁻¹) := by
      calc (n * ρ) ^ 3
          = n * (ρ * n * ρ⁻¹) * (ρ * ρ * n * (ρ * ρ)⁻¹) * (ρ * ρ * ρ) := by
              rw [pow_three']; group
        _ = n * (ρ * n * ρ⁻¹) * (ρ * ρ * n * (ρ * ρ)⁻¹) := by rw [hρ3', mul_one]
    rw [hw3eq]
    exact N.mul_mem (N.mul_mem hnN hn1) hn2
  exact ⟨w, rfl, hwconj, hwρ, hw3⟩

private theorem inv_mod_e_data {N : Subgroup G} (hN : IsPGroup 2 N) {ρ : G}
    (hρ : orderOf ρ = 3) :
    ∃ e q : ℕ, e = Nat.card N ^ 2 ∧ e = 3 * q + 1 ∧ ρ ∉ N := by
  let e : ℕ := Nat.card N ^ 2
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have he4 : e = 4 ^ k := by
    dsimp [e]
    rw [hk, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  have hemod : e % 3 = 1 := by
    have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
    have h := h4.pow k
    rw [he4]
    simpa [Nat.ModEq] using h
  obtain ⟨q, hq⟩ : ∃ q, e = 3 * q + 1 := by
    refine ⟨e / 3, ?_⟩
    have h := Nat.div_add_mod e 3
    omega
  have hρ_not_mem : ρ ∉ N := by
    intro hρmem
    obtain ⟨m, hm⟩ := hN.exists_orderOf_dvd_pow (⟨ρ, hρmem⟩ : N)
    rw [Subgroup.orderOf_mk, hρ] at hm
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hm
    norm_num at h32
  exact ⟨e, q, rfl, hq, hρ_not_mem⟩

private theorem inv_mod_exists_w' {N : Subgroup G} (hN : IsPGroup 2 N) {x ρ w : G}
    (hρ : orderOf ρ = 3) (hwconj : x * w * x⁻¹ = w⁻¹)
    (hwρ : w * ρ⁻¹ = x * ρ * x⁻¹ * ρ) (hw3 : w ^ 3 ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hinv : x * ρ * x⁻¹ * ρ ∈ N)
    (hw_norm : w ∈ Subgroup.normalizer (N : Set G)) :
    ∃ w' : G, orderOf w' = 3 ∧ x * w' * x⁻¹ = w'⁻¹ ∧ w' * ρ⁻¹ ∈ N ∧
      w' ∈ Subgroup.normalizer (N : Set G) := by
  obtain ⟨e, q, he, hq, hρ_not_mem⟩ := inv_mod_e_data hN hρ
  let w' : G := w ^ e
  have hw'3 : w' ^ 3 = 1 := by
    dsimp [w']
    rw [← pow_mul, mul_comm, pow_mul]
    have hcard : (w ^ 3) ^ Nat.card N = 1 := by
      let nN : N := ⟨w ^ 3, hw3⟩
      have h := pow_card_eq_one' (G := N) (x := nN)
      have h' : (nN : G) ^ Nat.card N = 1 := by
        simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg (fun z : N => (z : G)) h
      simpa [nN] using h'
    have he' : e = Nat.card N * Nat.card N := by rw [he, pow_two]
    rw [he', pow_mul, hcard, one_pow]
  have hw'ρ : w' * ρ⁻¹ ∈ N := by
    dsimp [w']
    rw [hq]
    have hpow : w ^ (3 * q + 1) = w * (w ^ 3) ^ q := by
      rw [show 3 * q + 1 = 1 + 3 * q by omega, pow_add, pow_one, ← pow_mul]
    rw [hpow]
    have hw3q : (w ^ 3) ^ q ∈ N := N.pow_mem hw3 q
    have hwrho : w * ρ⁻¹ ∈ N := by rw [hwρ]; exact hinv
    have hsplit : w * (w ^ 3) ^ q * ρ⁻¹ =
        (w * ρ⁻¹) * (ρ * (w ^ 3) ^ q * ρ⁻¹) := by group
    rw [hsplit]
    exact N.mul_mem hwrho (hρN _ hw3q)
  have hw'ne : w' ≠ 1 := by
    intro h1
    have hmem : ρ⁻¹ ∈ N := by
      have h := hw'ρ
      rw [h1, one_mul] at h
      exact h
    exact hρ_not_mem (by simpa using N.inv_mem hmem)
  have hw'ord : orderOf w' = 3 := orderOf_eq_prime hw'3 hw'ne
  have hw'_norm : w' ∈ Subgroup.normalizer (N : Set G) := by
    dsimp [w']
    exact (Subgroup.normalizer (N : Set G)).pow_mem hw_norm e
  exact ⟨w', hw'ord, by dsimp [w']; rw [← conj_pow, hwconj, inv_pow], hw'ρ, hw'_norm⟩

private theorem inv_mod_normalizer_mem {N : Subgroup G} {x ρ : G}
    (hx : x * x = 1) (hρ : orderOf ρ = 3)
    (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) :
    x ∈ Subgroup.normalizer (N : Set G) ∧ ρ ∈ Subgroup.normalizer (N : Set G) := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hρ3 : ρ ^ 3 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  have hρ3' : ρ * ρ * ρ = 1 := by rw [← pow_three', hρ3]
  have hx_norm : x ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hxN n
    · intro hn
      have h : x * (x * n * x⁻¹) * x⁻¹ ∈ N := hxN _ hn
      convert h using 1
      calc n = (x * x) * n * (x⁻¹ * x⁻¹) := by rw [hx, hxinv, hx, one_mul, mul_one]
        _ = x * (x * n * x⁻¹) * x⁻¹ := by group
  have hρ_norm : ρ ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact hρN n
    · intro hn
      have h1 : ρ * (ρ * n * ρ⁻¹) * ρ⁻¹ ∈ N := hρN _ hn
      have h2 : ρ * (ρ * (ρ * n * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ ∈ N := hρN _ h1
      convert h2 using 1
      symm
      calc ρ * (ρ * (ρ * n * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
          = (ρ * ρ * ρ) * n * (ρ * ρ * ρ)⁻¹ := by group
        _ = n := by rw [hρ3', inv_one, one_mul, mul_one]
  exact ⟨hx_norm, hρ_norm⟩

theorem exists_conj_inv_of_inv_mod {N : Subgroup G} (hN : IsPGroup 2 N) {x ρ : G}
    (hx : x * x = 1) (hρ : orderOf ρ = 3) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hinv : x * ρ * x⁻¹ * ρ ∈ N) :
    ∃ j ∈ N, (j * x * j⁻¹) * ρ * (j * x * j⁻¹)⁻¹ = ρ⁻¹ := by
  classical
  obtain ⟨w, hwdef, hwconj, hwρ, hw3⟩ := inv_mod_w_props hN hx hρ hρN hinv
  obtain ⟨hx_norm, hρ_norm⟩ := inv_mod_normalizer_mem hx hρ hxN hρN
  have hw_norm : w ∈ Subgroup.normalizer (N : Set G) := by
    rw [hwdef]
    exact (Subgroup.normalizer (N : Set G)).mul_mem
      ((Subgroup.normalizer (N : Set G)).mul_mem
        ((Subgroup.normalizer (N : Set G)).mul_mem hx_norm hρ_norm)
        ((Subgroup.normalizer (N : Set G)).inv_mem hx_norm))
      ((Subgroup.normalizer (N : Set G)).inv_mem hρ_norm)
  obtain ⟨w', hw'ord, hxw', hw'ρ, hw'_norm⟩ :=
    inv_mod_exists_w' hN hρ hwconj hwρ hw3 hρN hinv hw_norm
  let M := ↥(Subgroup.normalizer (N : Set G))
  let ρM : M := ⟨ρ, hρ_norm⟩
  let wM : M := ⟨w', hw'_norm⟩
  have hρM : orderOf ρM = 3 := by rw [Subgroup.orderOf_mk]; exact hρ
  have hwM : orderOf wM = 3 := by rw [Subgroup.orderOf_mk]; exact hw'ord
  have hcos : ρM * wM⁻¹ ∈ N.subgroupOf (Subgroup.normalizer (N : Set G)) := by
    rw [Subgroup.mem_subgroupOf]
    show ρ * w'⁻¹ ∈ N
    have h : w' * ρ⁻¹ ∈ N := hw'ρ
    simpa [mul_inv_rev] using N.inv_mem h
  obtain ⟨jM, hjM, hjconj⟩ :=
    CFSG.GroupTheory.exists_conj_of_order_three_of_mul_inv_mem
      (J := N.subgroupOf (Subgroup.normalizer (N : Set G)))
      (hN.comap_subtype (K := Subgroup.normalizer (N : Set G))) hρM hwM hcos
  refine ⟨(jM : G), Subgroup.mem_subgroupOf.mp hjM, ?_⟩
  have hjconjG : (jM : G) * w' * (jM : G)⁻¹ = ρ := by
    have h := congrArg (fun z : M => (z : G)) hjconj
    simpa [wM, ρM, M] using h
  calc ((jM : G) * x * (jM : G)⁻¹) * ρ * ((jM : G) * x * (jM : G)⁻¹)⁻¹
      = (jM : G) * x * (jM : G)⁻¹ * ((jM : G) * w' * (jM : G)⁻¹) *
          (jM : G) * x⁻¹ * (jM : G)⁻¹ := by rw [hjconjG]; group
    _ = (jM : G) * (x * w' * x⁻¹) * (jM : G)⁻¹ := by group
    _ = (jM : G) * w'⁻¹ * (jM : G)⁻¹ := by rw [hxw']
    _ = ρ⁻¹ := by rw [← hjconjG]; group

variable {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

private theorem commute_inv_k_center (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : G} (hxH : x ∈ H z)
    (hinv : x * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * x⁻¹ =
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹)
    (hq : qH (z := z) D ⟨x, hxH⟩ * (s1A * s2A⁻¹) = (s1A * s2A⁻¹) * qH (z := z) D ⟨x, hxH⟩) :
    (let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
     let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
     let xH : ↥(H z) := ⟨x, hxH⟩
     let kH : ↥(H z) := σH⁻¹ * (xH * σH * xH⁻¹)
     (kH : G) ∈ centerIn (J z) ∧ (kH : G) ∈ J z) := by
  dsimp only
  let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
  let xH : ↥(H z) := ⟨x, hxH⟩
  let kH : ↥(H z) := σH⁻¹ * (xH * σH * xH⁻¹)
  have hcomm : Commute (sigma1Nine (z := z) D) σ₂ := hc₂.symm
  have hσρ : Commute σH ρH := by
    dsimp [σH, ρH]
    have h1 : Commute (sigma1Nine (z := z) D * σ₂⁻¹) (sigma1Nine (z := z) D) :=
      (Commute.refl (sigma1Nine (z := z) D)).mul_left hcomm.symm.inv_left
    have h2 : Commute (sigma1Nine (z := z) D * σ₂⁻¹) σ₂ :=
      hcomm.mul_left (Commute.refl σ₂).inv_left
    exact h1.mul_right h2
  have hqσ : qH (z := z) D σH = s1A * s2A⁻¹ := by
    dsimp [σH]
    rw [map_mul, map_inv, qH_sigma1Nine (z := z) D, hq₂]
  have hqkH : qH (z := z) D kH = 1 := by
    dsimp [kH]
    simp only [map_mul, map_inv, hqσ]
    have hqx : qH (z := z) D xH * (s1A * s2A⁻¹) =
        (s1A * s2A⁻¹) * qH (z := z) D xH := hq
    rw [hqx]
    group
  have hkJ : (kH : G) ∈ J z :=
    Subgroup.mem_subgroupOf.mp ((J_mem_iff D kH).mpr hqkH)
  have hxρ : xH * ρH * xH⁻¹ = ρH⁻¹ := by
    apply Subtype.ext
    simpa [xH, ρH] using hinv
  have hxσρ' : Commute (xH * σH * xH⁻¹) ρH := by
    have h := hσρ.conj xH
    rw [hxρ] at h
    exact (Commute.inv_right_iff).mp h
  have hkcommρ : Commute kH ρH := by
    dsimp [kH]
    exact hσρ.inv_left.mul_left hxσρ'
  have hcent : (kH : G) ∈ centralizer ({((ρH : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h := congrArg (fun z : ↥(H z) => (z : G)) hkcommρ.eq
      simpa using h)
  have hinf : (kH : G) ∈ J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hkJ, by simpa [ρH] using hcent⟩
  have hkcenter : (kH : G) ∈ centerIn (J z) := by
    rwa [J_inf_centralizer_sigma1Nine_mul_eq_centerIn_J (z := z) D h hIII hσ₂ hq₂ hc₂] at hinf
  exact ⟨hkcenter, hkJ⟩

private theorem commute_inv_k_eq_one (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : G} (hxH : x ∈ H z)
    (hinv : x * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * x⁻¹ =
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹)
    (hq : qH (z := z) D ⟨x, hxH⟩ * (s1A * s2A⁻¹) = (s1A * s2A⁻¹) * qH (z := z) D ⟨x, hxH⟩) :
    (let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
     let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
     let xH : ↥(H z) := ⟨x, hxH⟩
     let kH : ↥(H z) := σH⁻¹ * (xH * σH * xH⁻¹)
     kH = 1) := by
  dsimp only
  let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
  let xH : ↥(H z) := ⟨x, hxH⟩
  let kH : ↥(H z) := σH⁻¹ * (xH * σH * xH⁻¹)
  have hσH3 : σH ^ 3 = 1 := by
    have h3 : orderOf ((σH : G)) = 3 :=
      orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
    rw [Subgroup.orderOf_coe] at h3
    rw [← h3]; exact pow_orderOf_eq_one σH
  have hdata : (kH : G) ∈ centerIn (J z) ∧ (kH : G) ∈ J z := by
    have h := commute_inv_k_center (z := z) D h hIII hσ₂ hq₂ hc₂ hxH hinv hq
    simpa [σH, ρH, xH, kH] using h
  obtain ⟨hkcenter, hkJ_mem⟩ := hdata
  have hconjZσ : conjZ z σH = 1 := by
    dsimp [σH]
    rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D,
      conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q),
      inv_one, mul_one]
  have hkcentσ : (kH : G) ∈ centralizer ({((σH : ↥(H z)) : G)} : Set G) :=
    centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := σH) hconjZσ hkcenter
  have hσkcomm : Commute σH kH :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hkcentσ).symm
  have hxσeq : xH * σH * xH⁻¹ = σH * kH := by
    dsimp [kH]
    group
  have hxσ3 : (xH * σH * xH⁻¹) ^ 3 = 1 := by
    calc (xH * σH * xH⁻¹) ^ 3 = xH * σH ^ 3 * xH⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [hσH3]; group
  have hkH3 : kH ^ 3 = 1 := by
    have h := hxσ3
    rw [hxσeq, hσkcomm.mul_pow, hσH3, one_mul] at h
    exact h
  have hkH1 : kH = 1 := by
    have h3 : orderOf kH ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hkH3
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3eq
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      obtain ⟨n, hn⟩ := (isPGroup_J (z := z) h).exists_orderOf_dvd_pow
        (⟨(kH : G), hkJ_mem⟩ : J z)
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, h3eq] at hn
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hn
      norm_num at h32
  simpa [σH, ρH, xH, kH] using hkH1

theorem commute_sigma1Nine_mul_inv_of_inv (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : G} (hxH : x ∈ H z)
    (hinv : x * ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * x⁻¹ =
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹)
    (hq : qH (z := z) D ⟨x, hxH⟩ * (s1A * s2A⁻¹) = (s1A * s2A⁻¹) * qH (z := z) D ⟨x, hxH⟩) :
    x * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * x := by
  classical
  let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
  let xH : ↥(H z) := ⟨x, hxH⟩
  let kH : ↥(H z) := σH⁻¹ * (xH * σH * xH⁻¹)
  have hkH1 : kH = 1 := by
    have h := commute_inv_k_eq_one (z := z) D h hIII hσ₂ hq₂ hc₂ hxH hinv hq
    simpa [σH, ρH, xH, kH] using h
  have hxσ : xH * σH * xH⁻¹ = σH := by
    have hk := hkH1
    dsimp [kH] at hk
    calc xH * σH * xH⁻¹ = σH * (σH⁻¹ * (xH * σH * xH⁻¹)) := by group
      _ = σH := by rw [hk, mul_one]
  have hval := congrArg (fun z : ↥(H z) => (z : G)) hxσ
  have hgconj : x * ((σH : ↥(H z)) : G) * x⁻¹ = ((σH : ↥(H z)) : G) := by
    simpa [xH, σH, Subgroup.coe_mul, Subgroup.coe_inv] using hval
  calc x * ((σH : ↥(H z)) : G) = (x * ((σH : ↥(H z)) : G) * x⁻¹) * x := by group
    _ = ((σH : ↥(H z)) : G) * x := by rw [hgconj]

private theorem qH_eq_exists_Jconj_inv (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : G} (hxH : x ∈ H z) (hx : x * x = 1)
    (hqx : qH (z := z) D ⟨x, hxH⟩ = uA * vA ∨ qH (z := z) D ⟨x, hxH⟩ = uA * vA * tA) :
    ∃ j ∈ J z, (j * x * j⁻¹) *
        ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * (j * x * j⁻¹)⁻¹ =
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹ := by
  classical
  let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
  let xH : ↥(H z) := ⟨x, hxH⟩
  have hqρ : qH (z := z) D ρH = s1A * s2A := by
    dsimp [ρH]; rw [map_mul, qH_sigma1Nine (z := z) D, hq₂]; rfl
  have huv_inv : (uA * vA) * (s1A * s2A) * (uA * vA)⁻¹ = (s1A * s2A)⁻¹ := by
    apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; decide +kernel
  have huvt_inv : (uA * vA * tA) * (s1A * s2A) * (uA * vA * tA)⁻¹ =
      (s1A * s2A)⁻¹ := by
    apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; decide +kernel
  have hxN : ∀ n ∈ J z, x * n * x⁻¹ ∈ J z := by
    intro n hn
    let nH : ↥(H z) := ⟨n, J_le_H (z := z) hn⟩
    have hnH : nH ∈ (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hn
    have h := hN.conj_mem nH hnH xH
    simpa [nH, xH] using Subgroup.mem_subgroupOf.mp h
  have hρN : ∀ n ∈ J z, ((ρH : ↥(H z)) : G) * n * ((ρH : ↥(H z)) : G)⁻¹ ∈ J z := by
    intro n hn
    let nH : ↥(H z) := ⟨n, J_le_H (z := z) hn⟩
    have hnH : nH ∈ (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hn
    have h := hN.conj_mem nH hnH ρH
    simpa [nH, ρH] using Subgroup.mem_subgroupOf.mp h
  have hqk : qH (z := z) D (xH * ρH * xH⁻¹ * ρH) = 1 := by
    simp only [map_mul, map_inv, hqρ]
    rcases hqx with hqx | hqx
    · rw [show qH (z := z) D xH = uA * vA by simpa [xH] using hqx, huv_inv]; group
    · rw [show qH (z := z) D xH = uA * vA * tA by simpa [xH] using hqx, huvt_inv]; group
  have hinvJ : x * ((ρH : ↥(H z)) : G) * x⁻¹ * ((ρH : ↥(H z)) : G) ∈ J z := by
    have hmem : xH * ρH * xH⁻¹ * ρH ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff D _).mpr hqk
    simpa [xH, ρH] using Subgroup.mem_subgroupOf.mp hmem
  have hρord : orderOf (((ρH : ↥(H z)) : G)) = 3 := by
    dsimp [ρH]; exact orderOf_sigma1Nine_mul (z := z) D h hσ₂ hq₂ hc₂
  exact exists_conj_inv_of_inv_mod (N := J z) (isPGroup_J (z := z) h)
    hx hρord hxN hρN hinvJ

private theorem qH_eq_exists_Jconj_mem_T2 (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : G} (hxH : x ∈ H z)
    (hqx : qH (z := z) D ⟨x, hxH⟩ = uA * vA ∨ qH (z := z) D ⟨x, hxH⟩ = uA * vA * tA)
    (hj : ∃ j ∈ J z, (j * x * j⁻¹) *
        ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G) * (j * x * j⁻¹)⁻¹ =
      ((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)⁻¹) :
    ∃ j ∈ J z, j * x * j⁻¹ ∈
      lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  classical
  let σH : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let ρH : ↥(H z) := sigma1Nine (z := z) D * σ₂
  let xH : ↥(H z) := ⟨x, hxH⟩
  obtain ⟨j, hjJ, hjconj⟩ := hj
  let jH : ↥(H z) := ⟨j, J_le_H (z := z) hjJ⟩
  have hx'H : j * x * j⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem (J_le_H (z := z) hjJ) hxH)
      ((H z).inv_mem (J_le_H (z := z) hjJ))
  let x'H : ↥(H z) := ⟨j * x * j⁻¹, hx'H⟩
  have hqj : qH (z := z) D jH = 1 :=
    (J_mem_iff D jH).mp (Subgroup.mem_subgroupOf.mpr hjJ)
  have hqx' : qH (z := z) D x'H = qH (z := z) D xH := by
    have hx'eq : x'H = jH * xH * jH⁻¹ := by
      apply Subtype.ext
      simp [x'H, jH, xH]
    rw [hx'eq, map_mul, map_mul, map_inv, hqj]
    group
  have hq'_comm : qH (z := z) D x'H * (s1A * s2A⁻¹) =
      (s1A * s2A⁻¹) * qH (z := z) D x'H := by
    rw [hqx']
    rcases hqx with hqx | hqx
    · rw [show qH (z := z) D xH = uA * vA by simpa [xH] using hqx]
      apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; decide +kernel
    · rw [show qH (z := z) D xH = uA * vA * tA by simpa [xH] using hqx]
      apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; decide +kernel
  have hx'σ : (j * x * j⁻¹) * ((σH : ↥(H z)) : G) =
      ((σH : ↥(H z)) : G) * (j * x * j⁻¹) :=
    commute_sigma1Nine_mul_inv_of_inv (z := z) D h hIII hσ₂ hq₂ hc₂ hx'H hjconj hq'_comm
  have hx'T : j * x * j⁻¹ ∈ lemma54T₂ D ((σH : ↥(H z)) : G) := by
    rw [lemma54T₂]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hx'H, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx'σ
    · refine Subgroup.mem_map.mpr ⟨x'H, ?_, rfl⟩
      rw [Subgroup.mem_comap, hqx']
      rcases hqx with hqx | hqx
      · rw [show qH (z := z) D xH = uA * vA by simpa [xH] using hqx]
        exact Subgroup.subset_closure (by simp)
      · rw [show qH (z := z) D xH = uA * vA * tA by simpa [xH] using hqx]
        have h1 : uA * vA ∈ Subgroup.closure ({tA, uA * vA} : Set A45) :=
          Subgroup.subset_closure (by simp)
        have h2 : tA ∈ Subgroup.closure ({tA, uA * vA} : Set A45) :=
          Subgroup.subset_closure (by simp)
        simpa using Subgroup.mul_mem _ h1 h2
  exact ⟨j, hjJ, hx'T⟩

theorem exists_conj_mem_lemma54T₂_of_qH_eq (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {x : G} (hxH : x ∈ H z) (hx : x * x = 1)
    (hqx : qH (z := z) D ⟨x, hxH⟩ = uA * vA ∨ qH (z := z) D ⟨x, hxH⟩ = uA * vA * tA) :
    ∃ j ∈ J z, j * x * j⁻¹ ∈ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  classical
  obtain ⟨j, hjJ, hjconj⟩ := qH_eq_exists_Jconj_inv (z := z) (D := D)
    h hIII hσ₂ hq₂ hc₂ hxH hx hqx
  exact qH_eq_exists_Jconj_mem_T2 (z := z) (D := D) h hIII hσ₂ hq₂ hc₂ hxH hqx
    ⟨j, hjJ, hjconj⟩

theorem exists_conj_mem_lemma54T₂_of_outer (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {y : G} (hyH : y ∈ H z) (hy : y * y = 1)
    (hcls : IsConj (qH (z := z) D ⟨y, hyH⟩) vA ∨ IsConj (qH (z := z) D ⟨y, hyH⟩) (uA * vA)) :
    ∃ c ∈ H z, c * y * c⁻¹ ∈ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) := by
  classical
  let yH : ↥(H z) := ⟨y, hyH⟩
  obtain ⟨a, ha⟩ : ∃ a : A45, a * qH (z := z) D yH * a⁻¹ = uA * vA ∨
      a * qH (z := z) D yH * a⁻¹ = uA * vA * tA := by
    rcases hcls with hcls | hcls
    · obtain ⟨a, ha⟩ := isConj_iff.mp (hcls.trans isConj_vA_uvt)
      exact ⟨a, Or.inr ha⟩
    · obtain ⟨a, ha⟩ := isConj_iff.mp hcls
      exact ⟨a, Or.inl ha⟩
  obtain ⟨c₀, hc₀⟩ := qH_surjective (z := z) D a
  let xH : ↥(H z) := c₀ * yH * c₀⁻¹
  have hqx : qH (z := z) D xH = uA * vA ∨ qH (z := z) D xH = uA * vA * tA := by
    have hxeq : qH (z := z) D xH = a * qH (z := z) D yH * a⁻¹ := by
      dsimp [xH]
      rw [map_mul, map_mul, map_inv, hc₀]
    rcases ha with ha | ha
    · left; rw [hxeq, ha]
    · right; rw [hxeq, ha]
  have hx2 : (xH : G) * (xH : G) = 1 := by
    have hxcoe : (xH : G) = (c₀ : G) * y * (c₀ : G)⁻¹ := by
      simp [xH, yH]
    rw [hxcoe, ← pow_two, conj_pow, pow_two, hy]
    group
  have hqx' : qH (z := z) D ⟨(xH : G), xH.2⟩ = uA * vA ∨
      qH (z := z) D ⟨(xH : G), xH.2⟩ = uA * vA * tA := by
    simpa using hqx
  obtain ⟨j, hjJ, hjT⟩ := exists_conj_mem_lemma54T₂_of_qH_eq (z := z) (D := D)
    h hIII hσ₂ hq₂ hc₂ (x := (xH : G)) xH.2 hx2 hqx'
  refine ⟨j * (c₀ : G), (H z).mul_mem (J_le_H (z := z) hjJ) c₀.2, ?_⟩
  have hmemeq : (j * (c₀ : G)) * y * (j * (c₀ : G))⁻¹ = j * (xH : G) * j⁻¹ := by
    dsimp [xH, yH]
    group
  rw [hmemeq]
  exact hjT

theorem isConj_tA_or_utA_of_forall_conj_not_mem_lemma54T₂ (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {y : G} (hyH : y ∈ H z) (hy : orderOf y = 2) (hyz : y ≠ z)
    (hbad : ∀ c ∈ H z,
      c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) :
    IsConj (qH (z := z) D ⟨y, hyH⟩) tA ∨ IsConj (qH (z := z) D ⟨y, hyH⟩) (uA * tA) := by
  classical
  let yH : ↥(H z) := ⟨y, hyH⟩
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy, pow_two] at h
  have hyHord : orderOf yH = 2 := by
    rw [← Subgroup.orderOf_coe, show (yH : G) = y from rfl, hy]
  by_contra hcon
  push Not at hcon
  by_cases hq1 : qH (z := z) D yH = 1
  · have hyJ : y ∈ J z := by
      have hmem : yH ∈ (J z).subgroupOf (H z) := (J_mem_iff D yH).mpr hq1
      simpa [yH] using Subgroup.mem_subgroupOf.mp hmem
    have hT₂ := isSylowOf_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂
    obtain ⟨c, hcH, hcT⟩ :=
      exists_conj_mem_isSylowOf_centralizer_sigma1Nine_mul_inv (z := z) D h P hP
        hσ₂ hq₂ hc₂ hT₂ y hyJ hy hyz
    exact hbad c hcH hcT
  · have hqord : orderOf (qH (z := z) D yH) = 2 := by
      have hdvd : orderOf (qH (z := z) D yH) ∣ 2 := by
        have h := orderOf_map_dvd (qH (z := z) D) yH
        rwa [hyHord] at h
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hq1
      · exact h2
    rcases qa45_involution_classes (qH (z := z) D yH) hqord with h1 | h2 | h3 | h4
    · exact hcon.1 h1
    · exact hcon.2 h2
    · obtain ⟨c, hcH, hcT⟩ := exists_conj_mem_lemma54T₂_of_outer (z := z) D h hIII
        hσ₂ hq₂ hc₂ hyH hy2 (Or.inl h3)
      exact hbad c hcH hcT
    · obtain ⟨c, hcH, hcT⟩ := exists_conj_mem_lemma54T₂_of_outer (z := z) D h hIII
        hσ₂ hq₂ hc₂ hyH hy2 (Or.inr h4)
      exact hbad c hcH hcT

end CFSG.RankThree.GF2n.Parrott
