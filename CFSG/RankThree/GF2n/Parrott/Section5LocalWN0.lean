module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalWLabel

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private theorem conjZ_sigma1Nine_mul_sigma2_inv_eq_one (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) :
    conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
  rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D]
  have h2 : conjZ z σ₂ = 1 :=
    conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
  rw [h2, inv_one, mul_one]

private theorem pow_three_sigma1Nine_mul_sigma2_inv_eq_one
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1 := by
  have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
    rw [← sigma1Nine_order (z := z) D]
    exact pow_orderOf_eq_one _
  have h2 : (σ₂⁻¹) ^ 3 = 1 := by
    have hp : σ₂ ^ 3 = 1 := by rw [← hσ₂]; exact pow_orderOf_eq_one σ₂
    rw [inv_pow, hp, inv_one]
  have hcomm' : Commute (sigma1Nine (z := z) D) σ₂⁻¹ :=
    (show Commute (sigma1Nine (z := z) D) σ₂ from hc₂.symm).inv_right
  rw [hcomm'.mul_pow, h1, h2, mul_one]

theorem exists_conj_eq_mul_z_of_not_mem_centerIn (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {n : G}
    (hn : n ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hnZ : n ∉ centerIn (J z)) :
    ∃ q ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
      q * n * q⁻¹ = n * z := by
  have hZσ := conjZ_sigma1Nine_mul_sigma2_inv_eq_one (z := z) D h hq₂
  have hσ3 := pow_three_sigma1Nine_mul_sigma2_inv_eq_one (z := z) D hσ₂ hc₂
  have hcenter : centerIn (J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) = centerIn (J z) :=
    centerIn_J_inf_centralizer_eq (z := z) h hσ3 hZσ
  have hnQ : n ∈ J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := hn
  have hnC : n ∉ Subgroup.centralizer (J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) : Set G) := by
    intro hc
    apply hnZ
    rw [← hcenter]
    exact Subgroup.mem_inf.mpr ⟨hnQ, hc⟩
  rw [Subgroup.mem_centralizer_iff] at hnC
  push Not at hnC
  obtain ⟨q, hq, hqne⟩ := hnC
  refine ⟨q, hq, ?_⟩
  have hqJ : q ∈ J z := (Subgroup.mem_inf.mp hq).1
  have hnJ : n ∈ J z := (Subgroup.mem_inf.mp hn).1
  have hzn : z * n = n * z :=
    (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) n (J_le_H hnJ)).symm
  have hc : q * n * q⁻¹ * n⁻¹ ∈ Subgroup.zpowers z := by
    simpa [commutatorElement_def] using
      commutator_mem_zpowers_z (z := z) h (x := q) (y := n) hqJ hnJ
  have hcne : q * n * q⁻¹ * n⁻¹ ≠ 1 := by
    intro h1
    apply hqne
    have h2 : q * n * q⁻¹ = n := by
      have h3 := congrArg (fun t => t * n) h1
      simpa [mul_assoc] using h3
    calc q * n = (q * n * q⁻¹) * q := by group
      _ = n * q := by rw [h2]
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two h.1 hc with h1 | h1
  · exact absurd h1 hcne
  · calc q * n * q⁻¹ = (q * n * q⁻¹ * n⁻¹) * n := by group
      _ = z * n := by rw [h1]
      _ = n * z := hzn

private theorem conjV_sigma1Nine_fixed_of_conj_eq_mul_centerIn (h : Tim79a.ParrottHyp z)
    {n e : G} (hnJ : n ∈ J z) (he : e ∈ centerIn (J z))
    (hconj : ((sigma1Nine (z := z) D : ↥(H z)) : G) * n *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ = n * e) :
    conjV h (sigma1Nine (z := z) D) (QuotientV.pi z ⟨n, hnJ⟩) =
      QuotientV.pi z ⟨n, hnJ⟩ := by
  rw [conjV_mk h (sigma1Nine (z := z) D) ⟨n, hnJ⟩]
  have hmul : (⟨n, hnJ⟩ * ⟨e, he.1⟩ : J z) =
      conjJ' z (sigma1Nine (z := z) D) ⟨n, hnJ⟩ := by
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    exact hconj.symm
  rw [← hmul, map_mul, (pi_eq_one_iff_mem_centerIn he.1).mpr he, mul_one]

theorem sigma1Nine_conj_ne_mul_of_not_mem_centerIn (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {n e : G}
    (hn : n ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G))
    (hnZ : n ∉ centerIn (J z)) (he : e ∈ centerIn (J z)) :
    ((sigma1Nine (z := z) D : ↥(H z)) : G) * n * ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ ≠
      n * e := by
  intro hconj
  obtain ⟨⟨hnJ, hnσ⟩, hnτ⟩ := Subgroup.mem_inf.mp hn
  have hfixσ : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨n, hnJ⟩) =
      QuotientV.pi z ⟨n, hnJ⟩ := by
    rw [conjV_mk h (sigma1Nine (z := z) D * σ₂⁻¹) ⟨n, hnJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc : n * ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) =
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) * n :=
      Subgroup.mem_centralizer_singleton_iff.mp hnσ
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hfixτ : conjV h τ (QuotientV.pi z ⟨n, hnJ⟩) = QuotientV.pi z ⟨n, hnJ⟩ := by
    rw [conjV_mk h τ ⟨n, hnJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    have hc : n * (τ : G) = (τ : G) * n := Subgroup.mem_centralizer_singleton_iff.mp hnτ
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hfix1 : conjV h (sigma1Nine (z := z) D) (QuotientV.pi z ⟨n, hnJ⟩) =
      QuotientV.pi z ⟨n, hnJ⟩ :=
    conjV_sigma1Nine_fixed_of_conj_eq_mul_centerIn (z := z) D h hnJ he hconj
  obtain ⟨w, hw⟩ := spinVecToV_surjective h P (QuotientV.pi z ⟨n, hnJ⟩)
  have hσcoords : ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) *
      (⟨sigma2, sigma2_mem_A⟩ : A45)⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    refine coord_fixed_sigma1Nine_mul_inv (z := z) D h P hP hq₂ ?_
    rw [hw]
    exact hfixσ
  have htcoords : ((rhoA tA : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    refine coord_fixed_of_qH_eq_tA (z := z) D h P hP hqτ ?_
    rw [hw]
    exact hfixτ
  have h1coords : ((rhoA (⟨sigma1, sigma1_mem_A⟩ : A45) : GL8) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w := by
    have h := coord_fixed_of_conjV_fixed (z := z) D h P hP
      (y := sigma1Nine (z := z) D) (w := w) ?_
    · rwa [qH_sigma1Nine (z := z) D] at h
    · rw [hw]
      exact hfix1
  have htrace := spin_trace_sigma1_of_fixed_sigma_t hσcoords htcoords
  have hw2 : w + w = 0 := funext fun i => CharTwo.add_self_eq_zero (w i)
  have htrace' : w + w + w = 0 := by simpa [h1coords] using htrace
  have hzero : w = 0 := by simpa [hw2] using htrace'
  have hpi : QuotientV.pi z ⟨n, hnJ⟩ = 1 := by
    rw [← hw, hzero, spinVecToV_zero h P]
  exact hnZ ((pi_eq_one_iff_mem_centerIn hnJ).mp hpi)

private theorem mem_normalizer_lemma54W_of_conj {σ τ g : G}
    (hgN : ∀ n ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G),
      g * n * g⁻¹ ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G))
    (hgτ : g * τ * g⁻¹ ∈ lemma54W z σ τ) :
    g ∈ Subgroup.normalizer (lemma54W z σ τ : Set G) := by
  let N : Subgroup G := J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G)
  have hW : lemma54W z σ τ = N ⊔ Subgroup.zpowers τ := rfl
  have hmap_le : (lemma54W z σ τ).map (MulAut.conj g).toMonoidHom ≤ lemma54W z σ τ := by
    rw [hW, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      intro n hn
      exact Subgroup.mem_sup_left (hgN n hn)
    · have hτ' : (MulAut.conj g).toMonoidHom τ ∈ lemma54W z σ τ := by
        rw [show (MulAut.conj g).toMonoidHom τ = g * τ * g⁻¹ from rfl]
        exact hgτ
      exact Subgroup.zpowers_le.mpr hτ'
  have hcard : Nat.card ((lemma54W z σ τ).map (MulAut.conj g).toMonoidHom) =
      Nat.card (lemma54W z σ τ) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hmap : (lemma54W z σ τ).map (MulAut.conj g).toMonoidHom = lemma54W z σ τ :=
    Subgroup.eq_of_le_of_card_ge hmap_le (by rw [hcard])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem mem_lemma54N₀_of_mem_J (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {q : G}
    (hq : q ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) :
    q ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  let S : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let N : Subgroup G := J z ⊓ centralizer ({S} : Set G) ⊓ centralizer ({(τ : G)} : Set G)
  have hqJ : q ∈ J z := (Subgroup.mem_inf.mp hq).1
  have hqσ : q ∈ centralizer ({S} : Set G) := (Subgroup.mem_inf.mp hq).2
  have hzN : z ∈ N :=
    centerIn_J_le_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
      (z_mem_centerIn_J h)
  have hzNle : Subgroup.zpowers z ≤ N := Subgroup.zpowers_le.mpr hzN
  have hconjN : ∀ g ∈ J z ⊓ centralizer ({S} : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    obtain ⟨hgJ, -⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨⟨hnJ, -⟩, -⟩ := Subgroup.mem_inf.mp hn
    have hc : n⁻¹ * g * n * g⁻¹ ∈ Subgroup.zpowers z := by
      simpa [commutatorElement_def] using
        commutator_mem_zpowers_z (z := z) h (x := n⁻¹) (y := g) ((J z).inv_mem hnJ) hgJ
    rw [show g * n * g⁻¹ = n * (n⁻¹ * g * n * g⁻¹) by group]
    exact N.mul_mem hn (hzNle hc)
  have hqτW : q * (τ : G) * q⁻¹ ∈ lemma54W z S (τ : G) := by
    refine (mem_lemma54W_of_isLemma54Label (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (x := q * (τ : G) * q⁻¹) (e := 1) (Subgroup.one_mem _) ?_).1
    exact ⟨q, hq, by simp⟩
  have hnormal : q ∈ Subgroup.normalizer (lemma54W z S (τ : G) : Set G) :=
    mem_normalizer_lemma54W_of_conj (z := z) (σ := S) (τ := (τ : G))
      (fun n hn => hconjN q hq n hn) hqτW
  unfold lemma54N₀
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hnormal, hqσ⟩, J_le_H hqJ⟩

theorem tau_mem_lemma54N₀ (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (τ : G) ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  let S : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let W : Subgroup G := lemma54W z S (τ : G)
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hτW : (τ : G) ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers (τ : G))
  have hτcent : (τ : G) ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact lemma54W_comm (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ x hx (τ : G) hτW
  have hnormal : (τ : G) ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer (W : Set G) hτcent
  have hcomm : Commute τ (sigma1Nine (z := z) D * σ₂⁻¹) :=
    (show Commute τ (sigma1Nine (z := z) D) from hτ₁).mul_right
      ((show Commute τ σ₂ from hτ₂).inv_right)
  have hS : (τ : G) * S = S * (τ : G) := by
    simpa [S] using congrArg (fun a : ↥(H z) => (a : G)) hcomm.eq
  unfold lemma54N₀
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
    ⟨hnormal, Subgroup.mem_centralizer_singleton_iff.mpr hS⟩, τ.2⟩

private theorem conj_mem_lemma54N_of_mem_H_centralizer {σ τ g : G} (hgH : g ∈ H z)
    (hgσ : g * σ = σ * g) (hgτ : g * τ = τ * g) :
    (∀ n ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G),
      g * n * g⁻¹ ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G)) ∧
      g * τ * g⁻¹ = τ := by
  have hσ' : g⁻¹ * σ = σ * g⁻¹ := by
    calc g⁻¹ * σ = g⁻¹ * (σ * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * σ) * g⁻¹ := by rw [hgσ]
      _ = σ * g⁻¹ := by group
  have hτ' : g⁻¹ * τ = τ * g⁻¹ := by
    calc g⁻¹ * τ = g⁻¹ * (τ * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * τ) * g⁻¹ := by rw [hgτ]
      _ = τ * g⁻¹ := by group
  constructor
  · intro n hn
    obtain ⟨⟨hnJ, hnσ⟩, hnτ⟩ := Subgroup.mem_inf.mp hn
    have hnσ' : n * σ = σ * n := Subgroup.mem_centralizer_singleton_iff.mp hnσ
    have hnτ' : n * τ = τ * n := Subgroup.mem_centralizer_singleton_iff.mp hnτ
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨conj_mem_J_of_mem_H (z := z) hgH hnJ, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g * n * g⁻¹) * σ = g * n * (g⁻¹ * σ) := by group
        _ = g * n * (σ * g⁻¹) := by rw [hσ']
        _ = g * (n * σ) * g⁻¹ := by group
        _ = g * (σ * n) * g⁻¹ := by rw [hnσ']
        _ = (g * σ) * n * g⁻¹ := by group
        _ = (σ * g) * n * g⁻¹ := by rw [hgσ]
        _ = σ * (g * n * g⁻¹) := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g * n * g⁻¹) * τ = g * n * (g⁻¹ * τ) := by group
        _ = g * n * (τ * g⁻¹) := by rw [hτ']
        _ = g * (n * τ) * g⁻¹ := by group
        _ = g * (τ * n) * g⁻¹ := by rw [hnτ']
        _ = (g * τ) * n * g⁻¹ := by group
        _ = (τ * g) * n * g⁻¹ := by rw [hgτ]
        _ = τ * (g * n * g⁻¹) := by group
  · calc g * τ * g⁻¹ = (τ * g) * g⁻¹ := by rw [hgτ]
      _ = τ := by rw [mul_assoc, mul_inv_cancel, mul_one]

theorem sigma1Nine_mem_lemma54N₀ (_h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) :
    ((sigma1Nine (z := z) D : ↥(H z)) : G) ∈
      lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  let S : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let g : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  have hcomm : Commute (sigma1Nine (z := z) D) (sigma1Nine (z := z) D * σ₂⁻¹) :=
    (Commute.refl _).mul_right
      ((show Commute (sigma1Nine (z := z) D) σ₂ from hc₂.symm).inv_right)
  have hgσ : g * S = S * g := by
    simpa [g, S] using congrArg (fun a : ↥(H z) => (a : G)) hcomm.eq
  have hgτ : g * (τ : G) = (τ : G) * g := by
    simpa [g] using congrArg (fun a : ↥(H z) => (a : G)) hτ₁.symm
  have hgH : g ∈ H z := (sigma1Nine (z := z) D).2
  obtain ⟨hgN, hgτconj⟩ :=
    conj_mem_lemma54N_of_mem_H_centralizer (z := z) (σ := S) (τ := (τ : G)) hgH hgσ hgτ
  have hgτW : g * (τ : G) * g⁻¹ ∈ lemma54W z S (τ : G) := by
    rw [hgτconj]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (τ : G))
  have hnormal : g ∈ Subgroup.normalizer (lemma54W z S (τ : G) : Set G) :=
    mem_normalizer_lemma54W_of_conj (z := z) (σ := S) (τ := (τ : G)) hgN hgτW
  unfold lemma54N₀
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hnormal,
    Subgroup.mem_centralizer_singleton_iff.mpr hgσ⟩, hgH⟩

theorem lemma54T₂_le_lemma54N₀ (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ≤
      lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
  intro g hg
  let S : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let W : Subgroup G := lemma54W z S (τ : G)
  let T : Subgroup G := lemma54T₂ D S
  have hT : IsSylowOf 2 T (H z ⊓ centralizer ({S} : Set G)) :=
    isSylowOf_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂
  have hWT : W ≤ T := lemma54W_le_lemma54T₂ (z := z) D (σ₂ := σ₂) hqτ hτ₁ hτ₂
  have hgT' : g ∈ H z ⊓ centralizer ({S} : Set G) := hT.le hg
  have hgH : g ∈ H z := (Subgroup.mem_inf.mp hgT').1
  have hgσ : g ∈ centralizer ({S} : Set G) := (Subgroup.mem_inf.mp hgT').2
  let E : Subgroup G := W.map (MulAut.conj g).toMonoidHom
  have hE_le : E ≤ T := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    change g * w * g⁻¹ ∈ T
    exact T.mul_mem (T.mul_mem hg (hWT hw)) (T.inv_mem hg)
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨wa, hwa, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨wb, hwb, rfl⟩ := Subgroup.mem_map.mp hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g * wa * g⁻¹) * (g * wb * g⁻¹) = g * (wa * wb) * g⁻¹ := by group
      _ = g * (wb * wa) * g⁻¹ := by
        rw [lemma54W_comm (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ wa hwa wb hwb]
      _ = (g * wb * g⁻¹) * (g * wa * g⁻¹) := by group
  have hEsq : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by
        rw [lemma54W_mul_self (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ w hw]
      _ = 1 := by group
  have hEcard : Nat.card E = 32 :=
    (Subgroup.card_map_of_injective (K := W) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).trans
      (card_lemma54W (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
  have hmap : W.map (MulAut.conj g).toMonoidHom = W :=
    eq_lemma54W_of_le_lemma54T₂ (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      E hE_le hEcomm hEsq hEcard
  have hnormal : g ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  unfold lemma54N₀
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hnormal, hgσ⟩, hgH⟩

theorem exists_mem_lemma54N₀_not_mem_centralizer_z1
    (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∃ μ ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      μ ∉ centralizer ({z₁} : Set G) := by
  by_contra hno
  push Not at hno
  let S : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  have hT : IsSylowOf 2 (lemma54T₂ D S) (H z ⊓ centralizer ({S} : Set G)) :=
    isSylowOf_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂
  have hz1N : z₁ ∈ J z ⊓ centralizer ({S} : Set G) ⊓ centralizer ({(τ : G)} : Set G) :=
    centerIn_J_le_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hz₁
  have hz1W : z₁ ∈ lemma54W z S (τ : G) := Subgroup.mem_sup_left hz1N
  have hz1T : z₁ ∈ lemma54T₂ D S :=
    lemma54W_le_lemma54T₂ (z := z) D (σ₂ := σ₂) hqτ hτ₁ hτ₂ hz1W
  have hTle : lemma54T₂ D S ≤ lemma54N₀ (z := z) S (τ : G) :=
    lemma54T₂_le_lemma54N₀ (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  have hT2C : lemma54T₂ D S ≤ centralizer ({z₁} : Set G) :=
    fun x hx => hno x (hTle hx)
  have hz1centT : z₁ ∈ centerIn (lemma54T₂ D S) :=
    Subgroup.mem_inf.mpr ⟨hz1T, Subgroup.mem_centralizer_iff.mpr
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mp (hT2C ht))⟩
  have hz1in : z₁ ∈ centerIn (lemma54T₂ D S) ⊓ centerIn (J z) :=
    Subgroup.mem_inf.mpr ⟨hz1centT, hz₁⟩
  have hzEq := centerIn_inf_centerIn_J_eq_zpowers_of_isSylowOf_centralizer_sigma1Nine_mul_inv
    (z := z) D h hZ hσ₂ hq₂ hc₂ hT
  rw [hzEq] at hz1in
  exact hz₁z hz1in

end CFSG.RankThree.GF2n.Parrott
