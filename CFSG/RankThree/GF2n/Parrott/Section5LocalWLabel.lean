module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalW
public import CFSG.RankThree.GF2n.Parrott.Section5LocalJ
public import CFSG.RankThree.GF2n.Parrott.Section5Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix commutatorElement

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def IsLemma54Label (σ τ x e : G) : Prop :=
  ∃ q ∈ J z ⊓ centralizer ({σ} : Set G), x = q * τ * q⁻¹ * e

@[expose] noncomputable def lemma54N₀ (σ τ : G) : Subgroup G :=
  normalizer (lemma54W z σ τ : Set G) ⊓ centralizer ({σ} : Set G) ⊓ H z

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem centerIn_J_le_lemma54N (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    centerIn (J z) ≤ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) := by
  intro e he
  have heJ : e ∈ J z := he.1
  have hπe : QuotientV.pi z ⟨e, heJ⟩ = 1 := (pi_eq_one_iff_mem_centerIn heJ).mpr he
  have hσfix : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨e, heJ⟩) =
      QuotientV.pi z ⟨e, heJ⟩ := by rw [hπe, map_one]
  have hτfix : conjV h τ (QuotientV.pi z ⟨e, heJ⟩) = QuotientV.pi z ⟨e, heJ⟩ := by
    rw [hπe, map_one]
  obtain ⟨hσe, hτe⟩ := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    ⟨e, heJ⟩ hσfix hτfix
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨heJ, hσe⟩, hτe⟩

theorem eq_one_of_conj_tau_eq_mul (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {q e : G}
    (hq : q ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (he : e ∈ centerIn (J z)) (hqe : q * (τ : G) * q⁻¹ = (τ : G) * e) :
    e = 1 := by
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hqJ : q ∈ J z := hq.1
  have hqσ : q ∈ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := hq.2
  have heJ : e ∈ J z := he.1
  have hπe : QuotientV.pi z ⟨e, heJ⟩ = 1 := (pi_eq_one_iff_mem_centerIn heJ).mpr he
  have hconj : (τ : G) * q * (τ : G)⁻¹ = e * q := by
    rw [inv_eq_of_mul_eq_one_right hτG]
    calc (τ : G) * q * (τ : G) = (τ : G) * (q * (τ : G) * q⁻¹) * q := by group
      _ = (τ : G) * ((τ : G) * e) * q := by rw [hqe]
      _ = e * q := by rw [← mul_assoc, hτG, one_mul]
  have hτfix : conjV h τ (QuotientV.pi z ⟨q, hqJ⟩) = QuotientV.pi z ⟨q, hqJ⟩ := by
    rw [conjV_mk h τ ⟨q, hqJ⟩]
    have hcoe : ((conjJ' z τ ⟨q, hqJ⟩ : J z) : G) = e * q := by
      rw [conjJ'_apply_coe]
      exact hconj
    rw [show conjJ' z τ ⟨q, hqJ⟩ = ⟨e * q, (J z).mul_mem heJ hqJ⟩ from Subtype.ext hcoe]
    calc QuotientV.pi z ⟨e * q, (J z).mul_mem heJ hqJ⟩
        = QuotientV.pi z (⟨e, heJ⟩ * ⟨q, hqJ⟩) := rfl
      _ = QuotientV.pi z ⟨e, heJ⟩ * QuotientV.pi z ⟨q, hqJ⟩ := map_mul _ _ _
      _ = QuotientV.pi z ⟨q, hqJ⟩ := by rw [hπe, one_mul]
  have hσfix : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨q, hqJ⟩) =
      QuotientV.pi z ⟨q, hqJ⟩ := by
    rw [conjV_mk h _ ⟨q, hqJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe, ← Subgroup.mem_centralizer_singleton_iff.mp hqσ]
    group
  obtain ⟨-, hqτ⟩ := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    ⟨q, hqJ⟩ hσfix hτfix
  have hcomm : q * (τ : G) = (τ : G) * q := Subgroup.mem_centralizer_singleton_iff.mp hqτ
  have h1 : (τ : G) * e = (τ : G) := by
    rw [← hqe, hcomm, mul_inv_cancel_right]
  exact mul_left_cancel (h1.trans (mul_one (τ : G)).symm)

private theorem conj_eq_of_conj_mul_eq {q q' τ e e' : G} (hq' : q' ∈ J z)
    (he : e ∈ centerIn (J z)) (he' : e' ∈ centerIn (J z))
    (heq : q * τ * q⁻¹ * e = q' * τ * q'⁻¹ * e') :
    (q'⁻¹ * q) * τ * (q'⁻¹ * q)⁻¹ * e = τ * e' := by
  have hce : e * q' = q' * e := (Subgroup.mem_centralizer_iff.mp he.2 q' hq').symm
  have hce' : e' * q' = q' * e' := (Subgroup.mem_centralizer_iff.mp he'.2 q' hq').symm
  have h1 := congrArg (fun t => q'⁻¹ * t * q') heq
  have hL : q'⁻¹ * (q * τ * q⁻¹ * e) * q' = (q'⁻¹ * q) * τ * (q'⁻¹ * q)⁻¹ * e := by
    rw [show q'⁻¹ * (q * τ * q⁻¹ * e) * q' = q'⁻¹ * (q * τ * q⁻¹ * (e * q')) by group, hce]
    group
  have hR : q'⁻¹ * (q' * τ * q'⁻¹ * e') * q' = τ * e' := by
    rw [show q'⁻¹ * (q' * τ * q'⁻¹ * e') * q' = q'⁻¹ * (q' * τ * q'⁻¹ * (e' * q')) by group,
      hce']
    group
  rw [hL, hR] at h1
  exact h1

theorem isLemma54Label_unique (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {x e e' : G} (he : e ∈ centerIn (J z)) (he' : e' ∈ centerIn (J z))
    (hx : IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e)
    (hx' : IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e') :
    e = e' := by
  obtain ⟨q, hq, hqx⟩ := hx
  obtain ⟨q', hq', hqx'⟩ := hx'
  have heq : q * (τ : G) * q⁻¹ * e = q' * (τ : G) * q'⁻¹ * e' := by rw [← hqx, ← hqx']
  have hmain := conj_eq_of_conj_mul_eq (z := z) hq'.1 he he' heq
  have hQ : q'⁻¹ * q ∈ J z ⊓
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_inf.mpr
      ⟨(J z).mul_mem ((J z).inv_mem hq'.1) hq.1,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hq'.2) hq.2⟩
  have hee' : e' * e⁻¹ ∈ centerIn (J z) :=
    Subgroup.mul_mem _ he' (Subgroup.inv_mem _ he)
  have hconj : q'⁻¹ * q * (τ : G) * (q'⁻¹ * q)⁻¹ = (τ : G) * (e' * e⁻¹) := by
    calc q'⁻¹ * q * (τ : G) * (q'⁻¹ * q)⁻¹
        = (q'⁻¹ * q * (τ : G) * (q'⁻¹ * q)⁻¹ * e) * e⁻¹ := by group
      _ = ((τ : G) * e') * e⁻¹ := by rw [hmain]
      _ = (τ : G) * (e' * e⁻¹) := by group
  have h2 := eq_one_of_conj_tau_eq_mul (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hQ hee' hconj
  exact (mul_inv_eq_one.mp h2).symm

private theorem pi_inv_eq_pi_label (h : Tim79a.ParrottHyp z) (y : J z) :
    QuotientV.pi z y⁻¹ = QuotientV.pi z y := by
  rw [map_inv]
  have h2 : QuotientV.pi z y * QuotientV.pi z y = 1 := by
    have h3 := QuotientV.pow_two_eq_one_V h (QuotientV.pi z y)
    rwa [pow_two] at h3
  exact inv_eq_of_mul_eq_one_right h2

private theorem tau_mem_centralizer_sigmaLabel {σ₂ τ : ↥(H z)}
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (τ : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
  have h2 : τ * σ₂⁻¹ = σ₂⁻¹ * τ := (show Commute τ σ₂ from hτ₂).inv_right.eq
  have hcomm : τ * (sigma1Nine (z := z) D * σ₂⁻¹) =
      (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by
    calc τ * (sigma1Nine (z := z) D * σ₂⁻¹) = (τ * sigma1Nine D) * σ₂⁻¹ := by group
      _ = (sigma1Nine D * τ) * σ₂⁻¹ := by rw [hτ₁]
      _ = sigma1Nine D * (τ * σ₂⁻¹) := by group
      _ = sigma1Nine D * (σ₂⁻¹ * τ) := by rw [h2]
      _ = (sigma1Nine D * σ₂⁻¹) * τ := by group
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)

private theorem not_mem_J_of_qH_eq_tA_label {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) :
    (τ : G) ∉ J z := by
  intro hmem
  have hq1 : qH (z := z) D τ = 1 := (J_mem_iff D τ).mp (Subgroup.mem_subgroupOf.mpr hmem)
  rw [hqτ] at hq1
  exact t_ne_one (congrArg Subtype.val hq1)

private theorem commutator_tau_mem_lemma54N (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {q : G} (hq : q ∈ J z ⊓
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) :
    q * (τ : G) * q⁻¹ * (τ : G)⁻¹ ∈ J z ⊓
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) := by
  have hqJ : q ∈ J z := hq.1
  have hqσ : q ∈ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := hq.2
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hτσ : (τ : G) ∈ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    tau_mem_centralizer_sigmaLabel (z := z) D hτ₁ hτ₂
  set c : G := q * (τ : G) * q⁻¹ * (τ : G)⁻¹ with hc
  have hcJ : c ∈ J z := by
    rw [hc, show q * (τ : G) * q⁻¹ * (τ : G)⁻¹ =
      q * ((τ : G) * q⁻¹ * (τ : G)⁻¹) by group]
    exact (J z).mul_mem hqJ (conj_mem_J_of_mem_H τ.2 ((J z).inv_mem hqJ))
  have hcσ : c ∈ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) := by
    rw [hc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hqσ hτσ)
      (Subgroup.inv_mem _ hqσ)) (Subgroup.inv_mem _ hτσ)
  have hcτ : (τ : G) * c * (τ : G)⁻¹ = c⁻¹ := by
    have hτinv : (τ : G)⁻¹ = (τ : G) := inv_eq_of_mul_eq_one_right hτG
    rw [hc, show (q * (τ : G) * q⁻¹ * (τ : G)⁻¹)⁻¹ =
      (τ : G) * q * (τ : G)⁻¹ * q⁻¹ by group, hτinv]
    simp only [mul_assoc, hτG, mul_one]
  have hfixc : conjV h τ (QuotientV.pi z ⟨c, hcJ⟩) = QuotientV.pi z ⟨c, hcJ⟩ := by
    have hconjc : conjJ' z τ ⟨c, hcJ⟩ = ⟨c, hcJ⟩⁻¹ := by
      apply Subtype.ext
      rw [conjJ'_apply_coe, Subgroup.coe_inv]
      exact hcτ
    rw [conjV_mk h τ ⟨c, hcJ⟩, hconjc, pi_inv_eq_pi_label (z := z) h]
  have hfixσ : conjV h (sigma1Nine (z := z) D * σ₂⁻¹) (QuotientV.pi z ⟨c, hcJ⟩) =
      QuotientV.pi z ⟨c, hcJ⟩ := by
    rw [conjV_mk h _ ⟨c, hcJ⟩]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe, ← Subgroup.mem_centralizer_singleton_iff.mp hcσ]
    group
  obtain ⟨-, hcCentral⟩ := mem_centralizer_of_conjV_pi_eq (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ
    hτ₁ hτ₂ ⟨c, hcJ⟩ hfixσ hfixc
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcJ, hcσ⟩, hcCentral⟩

theorem mem_lemma54W_of_isLemma54Label (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {x e : G} (he : e ∈ centerIn (J z))
    (hx : IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e) :
    x ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∧ x ∉ J z := by
  obtain ⟨q, hq, rfl⟩ := hx
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hcN := commutator_tau_mem_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq
  have hcJ : q * (τ : G) * q⁻¹ * (τ : G)⁻¹ ∈ J z := (Subgroup.mem_inf.mp hcN).1.1
  have heN : e ∈ J z ⊓
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) :=
    centerIn_J_le_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ he
  have hxeq : q * (τ : G) * q⁻¹ * e =
      (q * (τ : G) * q⁻¹ * (τ : G)⁻¹) * (τ : G) * e := by group
  have hxW : q * (τ : G) * q⁻¹ * e ∈
      lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
    rw [hxeq]
    exact (lemma54W _ _ _).mul_mem ((lemma54W _ _ _).mul_mem
      (Subgroup.mem_sup_left hcN) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      (Subgroup.mem_sup_left heN)
  refine ⟨hxW, ?_⟩
  intro hxJ
  have hmem : (q * (τ : G) * q⁻¹ * (τ : G)⁻¹) * (τ : G) * e ∈ J z := hxeq ▸ hxJ
  have hτmem : (τ : G) ∈ J z := by
    rw [show (τ : G) = (q * (τ : G) * q⁻¹ * (τ : G)⁻¹)⁻¹ *
      ((q * (τ : G) * q⁻¹ * (τ : G)⁻¹) * (τ : G) * e) * e⁻¹ by group]
    exact (J z).mul_mem ((J z).mul_mem ((J z).inv_mem hcJ) hmem) ((J z).inv_mem he.1)
  exact not_mem_J_of_qH_eq_tA_label (z := z) D hqτ hτmem

private theorem card_autFixedSubgroup_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) :
    Nat.card ↥(autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹))) = 16 := by
  have hqσ : qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹ := by
    rw [map_mul, map_inv, qH_sigma1Nine (z := z) D, hq₂]
  let e : (Fin 8 → ZMod 2) ≃ QuotientV.V z :=
    { toFun := spinVecToV h P
      invFun := fun v => (spinVecToV_surjective h P v).choose
      left_inv := fun w => spinVecToV_injective h P
        (spinVecToV_surjective h P (spinVecToV h P w)).choose_spec
      right_inv := fun v => (spinVecToV_surjective h P v).choose_spec }
  have h1 : Nat.card ↥(autFixedSubgroup (conjV h (sigma1Nine (z := z) D * σ₂⁻¹))) =
      Nat.card {w : Fin 8 → ZMod 2 // ((rhoA ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹) : GL8) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w} :=
    (Nat.card_congr (Equiv.subtypeEquiv e (fun w => by
      have hew : e w = spinVecToV h P w := rfl
      rw [hew, mem_autFixedSubgroup]
      constructor
      · intro hw
        rw [conjV_spinVecToV (z := z) D h P hP, hqσ, hw]
      · intro hw
        rw [conjV_spinVecToV (z := z) D h P hP, hqσ] at hw
        exact spinVecToV_injective h P hw))).symm
  rw [h1, Nat.card_eq_fintype_card]
  exact spinFixedCard_sigma1_mul_sigma2_inv

private theorem card_centralizerJ_inf_center_sigma1Nine_mul_inv (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hq₂ : qH (z := z) D σ₂ = s2A) :
    Nat.card ↥(centralizerJ (sigma1Nine (z := z) D * σ₂⁻¹) ⊓ Subgroup.center (J z)) = 4 := by
  have hZσ : conjZ z (sigma1Nine (z := z) D * σ₂⁻¹) = 1 := by
    rw [map_mul, map_inv, conjZ_sigma1Nine (z := z) h D]
    have h2 : conjZ z σ₂ = 1 :=
      conjZ_eq_one_of_qH_mem_QP45 (z := z) D h σ₂ (by rw [hq₂]; exact sigma2_mem_Q)
    rw [h2, inv_one, mul_one]
  have hle : Subgroup.center (J z) ≤ centralizerJ (sigma1Nine (z := z) D * σ₂⁻¹) := by
    intro j hj
    rw [mem_centralizerJ_iff]
    have hjZ : (j : G) ∈ centerIn (J z) := by
      have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
        rwa [QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mp hj'
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hZσ hjZ)
  rw [inf_eq_right.mpr hle, card_center_subgroupOf_J (z := z) h]

private theorem card_J_inf_centralizer_sigmaLabel (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    Nat.card ↥(J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) = 2 ^ 6 := by
  let σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  have hcube : σ ^ 3 = 1 := by
    have h1 : (sigma1Nine (z := z) D) ^ 3 = 1 := by
      rw [← sigma1Nine_order (z := z) D]
      exact pow_orderOf_eq_one _
    have h2 : (σ₂⁻¹) ^ 3 = 1 := by
      rw [inv_pow, ← hσ₂, pow_orderOf_eq_one, inv_one]
    have hcomm : Commute (sigma1Nine (z := z) D) σ₂⁻¹ :=
      (show Commute (sigma1Nine (z := z) D) σ₂ from hc₂.symm).inv_right
    change (sigma1Nine (z := z) D * σ₂⁻¹) ^ 3 = 1
    rw [hcomm.mul_pow, h1, h2, mul_one]
  have hJcard : Nat.card (centralizerJ σ) = 2 ^ 6 := by
    rw [card_centralizerJ_eq_card_inf_mul_card_autFixed (z := z) h (by
        rw [card_J h]
        exact Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one hcube) (by decide)),
      card_centralizerJ_inf_center_sigma1Nine_mul_inv (z := z) D h hq₂,
      card_autFixedSubgroup_sigma1Nine_mul_inv (z := z) D h P hP hq₂]
    norm_num
  have hcard : Nat.card (centralizerJ σ) =
      Nat.card ↥(J z ⊓ centralizer ({(σ : G)} : Set G)) := by
    rw [centralizerJ, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := J z ⊓ centralizer ({(σ : G)} : Set G)) (K := J z) inf_le_left).toEquiv
  rw [← hJcard, hcard]

private theorem card_stabilizer_isLemma54Label (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    [MulAction ↥(J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) G]
    (hsmul : ∀ (q : ↥(J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))) (y : G),
      q • y = (q : G) * y * (q : G)⁻¹) :
    Nat.card (MulAction.stabilizer ↥(J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ((τ : G))) = 16 := by
  have hK : ∀ q : ↥(J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)),
      q ∈ MulAction.stabilizer _ ((τ : G)) ↔
        (q : G) ∈ J z ⊓
          centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
          centralizer ({(τ : G)} : Set G) := by
    intro q
    rw [MulAction.mem_stabilizer_iff, hsmul]
    constructor
    · intro hq
      refine Subgroup.mem_inf.mpr ⟨q.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (q : G) * (τ : G) = ((q : G) * (τ : G) * (q : G)⁻¹) * (q : G) := by group
        _ = (τ : G) * (q : G) := by rw [hq]
    · intro hq
      have hqτ : Commute (q : G) (τ : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hq.2
      rw [hqτ.eq]
      group
  have heq : MulAction.stabilizer ↥(J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) ((τ : G)) =
      (J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G)).subgroupOf
        (J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)) := by
    ext q
    rw [Subgroup.mem_subgroupOf, hK q]
  rw [heq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) ≤
      J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)
      from inf_le_left)).toEquiv]
  exact card_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂

private theorem card_orbit_isLemma54Label {τ : G} {Q : Subgroup G} [MulAction ↥Q G]
    (hstab : Nat.card (MulAction.stabilizer ↥Q τ) = 16) (hQB : Nat.card ↥Q = 64) :
    Nat.card ↥(MulAction.orbit ↥Q τ) = 4 := by
  rw [Nat.card_coe_set_eq]
  have hcount : Nat.card (MulAction.stabilizer ↥Q τ) * (MulAction.orbit ↥Q τ).ncard =
      Nat.card ↥Q := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  rw [hstab, hQB] at hcount
  omega

private theorem label_set_card_eq_orbit {σ τ e : G} {Q : Subgroup G} [MulAction ↥Q G]
    (hQ : Q = J z ⊓ centralizer ({σ} : Set G))
    (hsmul : ∀ (q : ↥Q) (y : G), q • y = (q : G) * y * (q : G)⁻¹) :
    Nat.card {x : G // IsLemma54Label (z := z) σ τ x e} =
      Nat.card ↥(MulAction.orbit ↥Q τ) := by
  let f : {x : G // IsLemma54Label (z := z) σ τ x e} → ↥(MulAction.orbit ↥Q τ) :=
    fun p => ⟨p.1 * e⁻¹, by
      obtain ⟨q, hq, hxq⟩ := p.2
      have hqQ : q ∈ Q := by rw [hQ]; exact hq
      have hb : (⟨q, hqQ⟩ : ↥Q) • τ = p.1 * e⁻¹ := by rw [hsmul, hxq]; group
      exact ⟨⟨q, hqQ⟩, hb⟩⟩
  let g : ↥(MulAction.orbit ↥Q τ) → {x : G // IsLemma54Label (z := z) σ τ x e} :=
    fun p => ⟨p.1 * e, by
      obtain ⟨q, hq⟩ := p.2
      have hb : (q : G) * τ * (q : G)⁻¹ = p.1 := by
        have hq' : (q : ↥Q) • τ = p.1 := hq
        rw [hsmul] at hq'
        exact hq'
      refine ⟨q, ?_, by rw [hb]⟩
      rw [← hQ]
      exact q.2⟩
  exact Nat.card_congr ⟨f, g, fun p => Subtype.ext (by change (p.1 * e⁻¹) * e = p.1; group),
    fun p => Subtype.ext (by change (p.1 * e) * e⁻¹ = p.1; group)⟩

theorem ncard_setOf_isLemma54Label (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (_hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {e : G} (_he : e ∈ centerIn (J z)) :
    {x : G |
      IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e}.ncard =
        4 := by
  let Q₀ : Subgroup G := J z ⊓
    centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G)
  letI : MulAction ↥Q₀ G :=
    MulAction.compHom G ((MulEquiv.toMonoidHom ConjAct.toConjAct).comp Q₀.subtype)
  have hsmul : ∀ (q : ↥Q₀) (y : G), q • y = (q : G) * y * (q : G)⁻¹ :=
    fun q y => ConjAct.toConjAct_smul (q : G) y
  have hQB : Nat.card ↥Q₀ = 64 := by
    have h1 := card_J_inf_centralizer_sigmaLabel (z := z) D h P hP hσ₂ hq₂ hc₂
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num] at h1
    simpa [Q₀] using h1
  have hstab : Nat.card (MulAction.stabilizer ↥Q₀ ((τ : G))) = 16 :=
    card_stabilizer_isLemma54Label (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hsmul
  have horbcard : Nat.card ↥(MulAction.orbit ↥Q₀ ((τ : G))) = 4 :=
    card_orbit_isLemma54Label hstab hQB
  rw [← Nat.card_coe_set_eq]
  change Nat.card {x : G // IsLemma54Label (z := z)
    ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e} = 4
  rw [label_set_card_eq_orbit (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G))
    (τ := (τ : G)) rfl hsmul, horbcard]

private theorem lemma54W_inf_J {σ τ : G} (hτG : τ * τ = 1) (hτJ : τ ∉ J z) :
    lemma54W z σ τ ⊓ J z =
      J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({τ} : Set G) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyW, hyJ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyσ, hyτ⟩ := (mem_lemma54W_iff_of_mem_J (z := z) hτG hτJ hyJ).mp hyW
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyJ, hyσ⟩, hyτ⟩
  · intro hy
    obtain ⟨hyA, hyτ⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hyJ, hyσ⟩ := Subgroup.mem_inf.mp hyA
    exact Subgroup.mem_inf.mpr
      ⟨(mem_lemma54W_iff_of_mem_J (z := z) hτG hτJ hyJ).mpr ⟨hyσ, hyτ⟩, hyJ⟩

private theorem ncard_lemma54W_diff_J (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ((lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) : Set G) \
        (J z : Set G)).ncard = 16 := by
  set W : Subgroup G :=
    lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) with hW
  have hτG : (τ : G) * (τ : G) = 1 := by simpa using congrArg Subtype.val hτ
  have hτJ : (τ : G) ∉ J z := not_mem_J_of_qH_eq_tA_label (z := z) D hqτ
  have hWcard : (W : Set G).ncard = 32 := by
    rw [← Nat.card_coe_set_eq, hW]
    exact card_lemma54W (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  have hNcard : ((J z ⊓ centralizer
      ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) : Subgroup G) : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact card_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
  have hsub : ((W ⊓ J z : Subgroup G) : Set G) ⊆ (W : Set G) :=
    fun y hy => (Subgroup.mem_inf.mp hy).1
  have hset : ((W : Set G) \ (J z : Set G)) =
      ((W : Set G) \ ((W ⊓ J z : Subgroup G) : Set G)) := by
    ext y
    simp only [Set.mem_diff, SetLike.mem_coe, Subgroup.mem_inf]
    tauto
  rw [show ((lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) : Set G) \
      (J z : Set G)) = ((W : Set G) \ (J z : Set G)) from rfl]
  rw [hset, Set.ncard_sdiff' hsub (Set.toFinite _), hWcard,
    lemma54W_inf_J (z := z) hτG hτJ, hNcard]

theorem exists_isLemma54Label (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {x : G} (hxW : x ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
    (hxJ : x ∉ J z) :
    ∃ e ∈ centerIn (J z),
      IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e := by
  have hdiff := ncard_lemma54W_diff_J (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  let S : ↥(centerIn (J z)) → Set G := fun e =>
    {y : G | IsLemma54Label (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) y (e : G)}
  have hS4 : ∀ e : ↥(centerIn (J z)), (S e).ncard = 4 := fun e =>
    ncard_setOf_isLemma54Label (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ e.2
  have hSsub : ∀ e : ↥(centerIn (J z)), S e ⊆
      ((lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) : Set G) \
        (J z : Set G)) := fun e _y hy =>
    mem_lemma54W_of_isLemma54Label (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ e.2 hy
  have hdisj : Pairwise (fun e e' => Disjoint (S e) (S e')) := by
    intro e e' hne
    refine Set.disjoint_left.mpr (fun y hy hy' => hne (Subtype.ext ?_))
    exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ e.2 e'.2 hy hy'
  haveI : Fintype ↥(centerIn (J z)) := Fintype.ofFinite _
  have hUnion : (⋃ e : ↥(centerIn (J z)), S e).ncard = 16 := by
    rw [Set.ncard_iUnion_of_finite (fun e => Set.toFinite _) hdisj,
      finsum_eq_sum_of_fintype]
    simp only [hS4]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_centerIn_J h]
    norm_num
  have heq : (⋃ e : ↥(centerIn (J z)), S e) =
      ((lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) : Set G) \
        (J z : Set G)) :=
    Set.eq_of_subset_of_ncard_le (fun y hy => by
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hy
      exact hSsub e he) (by rw [hUnion, hdiff])
  have hxmem : x ∈ (⋃ e : ↥(centerIn (J z)), S e) := by
    rw [heq]
    exact ⟨hxW, hxJ⟩
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hxmem
  exact ⟨e, e.2, he⟩

theorem isLemma54Label_conj {σ τ g x e ℓ : G} (hgH : g ∈ H z)
    (hgσ : g ∈ centralizer ({σ} : Set G)) (hℓ : ℓ ∈ centerIn (J z))
    (hgτ : IsLemma54Label (z := z) σ τ (g * τ * g⁻¹) ℓ) (hx : IsLemma54Label (z := z) σ τ x e) :
    IsLemma54Label (z := z) σ τ (g * x * g⁻¹) (ℓ * (g * e * g⁻¹)) := by
  obtain ⟨q, hq, rfl⟩ := hx
  obtain ⟨q₁, hq₁, hq₁eq⟩ := hgτ
  have hqJ : q ∈ J z := hq.1
  have hqσ : q ∈ centralizer ({σ} : Set G) := hq.2
  have hq'J : g * q * g⁻¹ ∈ J z := conj_mem_J_of_mem_H hgH hqJ
  have hg_eq : g * σ = σ * g := Subgroup.mem_centralizer_singleton_iff.mp hgσ
  have hgi : g⁻¹ * σ = σ * g⁻¹ := (show Commute g σ from hg_eq).inv_left.eq
  have hq'σ : g * q * g⁻¹ ∈ centralizer ({σ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hq_eq : q * σ = σ * q := Subgroup.mem_centralizer_singleton_iff.mp hqσ
    calc (g * q * g⁻¹) * σ = g * q * (g⁻¹ * σ) := by group
      _ = g * q * (σ * g⁻¹) := by rw [hgi]
      _ = g * (q * σ) * g⁻¹ := by group
      _ = g * (σ * q) * g⁻¹ := by rw [hq_eq]
      _ = σ * (g * q * g⁻¹) := by
            rw [show g * (σ * q) * g⁻¹ = (g * σ) * q * g⁻¹ by group, hg_eq]
            group
  have hℓq' : ℓ * (g * q * g⁻¹) = (g * q * g⁻¹) * ℓ :=
    (Subgroup.mem_centralizer_iff.mp hℓ.2 (g * q * g⁻¹) hq'J).symm
  have hℓq'inv : ℓ * (g * q * g⁻¹)⁻¹ = (g * q * g⁻¹)⁻¹ * ℓ :=
    (show Commute ℓ (g * q * g⁻¹) from hℓq').inv_right.eq
  refine ⟨(g * q * g⁻¹) * q₁,
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hq'J hq₁.1, Subgroup.mul_mem _ hq'σ hq₁.2⟩, ?_⟩
  rw [show g * (q * τ * q⁻¹ * e) * g⁻¹ =
      (g * q * g⁻¹) * (g * τ * g⁻¹) * (g * q * g⁻¹)⁻¹ * (g * e * g⁻¹) by group, hq₁eq]
  rw [show (g * q * g⁻¹) * (q₁ * τ * q₁⁻¹ * ℓ) * (g * q * g⁻¹)⁻¹ * (g * e * g⁻¹) =
      (g * q * g⁻¹) * q₁ * τ * q₁⁻¹ * (ℓ * (g * q * g⁻¹)⁻¹) * (g * e * g⁻¹) by group,
    hℓq'inv]
  group

private theorem z_mul_self_label (h : Tim79a.ParrottHyp z) : z * z = 1 := by
  have h2 := pow_orderOf_eq_one z
  rw [h.1, pow_two] at h2
  exact h2

private theorem eq_one_or_eq_z_of_mem_zpowers (h : Tim79a.ParrottHyp z) {ζ : G}
    (hζ : ζ ∈ Subgroup.zpowers z) : ζ = 1 ∨ ζ = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hζ
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact z_mul_self_label h
  have hper : z ^ n = z ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · rw [hper, h0]; simp
  · rw [hper, h1]; simp

private theorem zpowers_z_commute_H (h : Tim79a.ParrottHyp z) {ζ : G}
    (hζ : ζ ∈ Subgroup.zpowers z) {x : G} (hx : x ∈ H z) : ζ * x = x * ζ :=
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.zpowers_le.mpr (z_centralizes_H h) hζ) x hx).symm

private theorem exists_zpowers_mul_comm (h : Tim79a.ParrottHyp z) {a b : G}
    (ha : a ∈ J z) (hb : b ∈ J z) :
    ∃ ζ ∈ Subgroup.zpowers z, a * b = b * a * ζ := by
  have hζ : ⁅a, b⁆ ∈ Subgroup.zpowers z := commutator_mem_zpowers_z h ha hb
  have hζ' : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := hζ
  refine ⟨a * b * a⁻¹ * b⁻¹, hζ', ?_⟩
  have hb' : (a * b * a⁻¹ * b⁻¹) * b = b * (a * b * a⁻¹ * b⁻¹) :=
    zpowers_z_commute_H h hζ' (J_le_H hb)
  have ha' : (a * b * a⁻¹ * b⁻¹) * a = a * (a * b * a⁻¹ * b⁻¹) :=
    zpowers_z_commute_H h hζ' (J_le_H ha)
  calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
    _ = b * (a * b * a⁻¹ * b⁻¹) * a := by rw [hb']
    _ = b * a * (a * b * a⁻¹ * b⁻¹) := by
          rw [show b * (a * b * a⁻¹ * b⁻¹) * a = b * ((a * b * a⁻¹ * b⁻¹) * a) by group,
            ha']
          group

private theorem commutator_mul_mem_J {t : G} (ht : t ∈ H z) {q : G} (hq : q ∈ J z) :
    q * t * q⁻¹ * t⁻¹ ∈ J z := by
  rw [show q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) by group]
  exact (J z).mul_mem hq (conj_mem_J_of_mem_H ht ((J z).inv_mem hq))

private theorem commutator_mul_tau_exists (h : Tim79a.ParrottHyp z) {q₁ q₂ t : G}
    (ht : t ∈ H z) (hq₁ : q₁ ∈ J z) (hq₂ : q₂ ∈ J z) :
    ∃ ζ ∈ Subgroup.zpowers z,
      (q₁ * q₂) * t * (q₁ * q₂)⁻¹ * t⁻¹ =
        (q₁ * t * q₁⁻¹ * t⁻¹) * (q₂ * t * q₂⁻¹ * t⁻¹) * ζ := by
  set c₁ : G := q₁ * t * q₁⁻¹ * t⁻¹ with hc₁
  set c₂ : G := q₂ * t * q₂⁻¹ * t⁻¹ with hc₂
  have hc₁J : c₁ ∈ J z := by rw [hc₁]; exact commutator_mul_mem_J ht hq₁
  have hc₂J : c₂ ∈ J z := by rw [hc₂]; exact commutator_mul_mem_J ht hq₂
  obtain ⟨ζ₁, hζ₁z, hζ₁⟩ := exists_zpowers_mul_comm h hq₁ hc₂J
  obtain ⟨ζ₂, hζ₂z, hζ₂⟩ := exists_zpowers_mul_comm h hc₂J hc₁J
  have hζ₁c₁ : ζ₁ * c₁ = c₁ * ζ₁ := zpowers_z_commute_H h hζ₁z (J_le_H hc₁J)
  have hζ₁c₂ : ζ₁ * c₂ = c₂ * ζ₁ := zpowers_z_commute_H h hζ₁z (J_le_H hc₂J)
  have hζ₁q₁ : ζ₁ * q₁⁻¹ = q₁⁻¹ * ζ₁ :=
    zpowers_z_commute_H h hζ₁z ((H z).inv_mem (J_le_H hq₁))
  have hstep1 : q₁ * c₂ * q₁⁻¹ = c₂ * ζ₁ := by
    rw [hζ₁, show c₂ * q₁ * ζ₁ * q₁⁻¹ = c₂ * q₁ * (ζ₁ * q₁⁻¹) by group, hζ₁q₁]
    group
  have hgoal : (q₁ * q₂) * t * (q₁ * q₂)⁻¹ * t⁻¹ = q₁ * c₂ * q₁⁻¹ * c₁ := by
    rw [hc₁, hc₂]; group
  refine ⟨ζ₁ * ζ₂, Subgroup.mul_mem _ hζ₁z hζ₂z, ?_⟩
  rw [hgoal, hstep1]
  calc c₂ * ζ₁ * c₁ = ζ₁ * (c₂ * c₁) := by rw [hζ₁c₂.symm]; group
    _ = ζ₁ * (c₁ * c₂ * ζ₂) := by rw [hζ₂]
    _ = c₁ * c₂ * (ζ₁ * ζ₂) := by
          rw [show ζ₁ * (c₁ * c₂ * ζ₂) = (ζ₁ * c₁) * c₂ * ζ₂ by group, hζ₁c₁,
            show c₁ * ζ₁ * c₂ * ζ₂ = c₁ * (ζ₁ * c₂) * ζ₂ by group, hζ₁c₂]
          group

private theorem eq_commutator_mul_of_label {τ q e n : G} (hτe : e * τ = τ * e)
    (h : n * τ = q * τ * q⁻¹ * e) :
    n = (q * τ * q⁻¹ * τ⁻¹) * e := by
  have hcomm : e * τ⁻¹ = τ⁻¹ * e := (show Commute e τ from hτe).inv_right.eq
  have h1 : n = (n * τ) * τ⁻¹ := by group
  rw [h1, h, show q * τ * q⁻¹ * e * τ⁻¹ = q * τ * q⁻¹ * (e * τ⁻¹) by group, hcomm]
  group

private theorem mul_tau_calc {τ Q c₁ c₂ e₁ e₂ ζ : G}
    (hc_eq : c₁ * c₂ = (Q * τ * Q⁻¹ * τ⁻¹) * ζ⁻¹)
    (he₁c₂ : e₁ * c₂ = c₂ * e₁) (heτ : e₁ * e₂ * τ = τ * (e₁ * e₂))
    (hζτ : ζ⁻¹ * τ = τ * ζ⁻¹) (hζe : ζ⁻¹ * (e₁ * e₂) = (e₁ * e₂) * ζ⁻¹) :
    (c₁ * e₁) * (c₂ * e₂) * τ = Q * τ * Q⁻¹ * (e₁ * e₂ * ζ⁻¹) := by
  calc (c₁ * e₁) * (c₂ * e₂) * τ = c₁ * c₂ * (e₁ * e₂) * τ := by
        rw [show (c₁ * e₁) * (c₂ * e₂) * τ = c₁ * (e₁ * c₂) * e₂ * τ by group, he₁c₂]
        group
    _ = c₁ * c₂ * ((e₁ * e₂) * τ) := by group
    _ = c₁ * c₂ * (τ * (e₁ * e₂)) := by rw [heτ]
    _ = c₁ * c₂ * τ * (e₁ * e₂) := by group
    _ = ((Q * τ * Q⁻¹ * τ⁻¹) * ζ⁻¹) * τ * (e₁ * e₂) := by rw [← hc_eq]
    _ = (Q * τ * Q⁻¹ * τ⁻¹) * ((τ * (ζ⁻¹ * (e₁ * e₂)))) := by
          rw [show ((Q * τ * Q⁻¹ * τ⁻¹) * ζ⁻¹) * τ * (e₁ * e₂) =
            (Q * τ * Q⁻¹ * τ⁻¹) * (ζ⁻¹ * τ) * (e₁ * e₂) by group, hζτ]
          group
    _ = (Q * τ * Q⁻¹) * ((e₁ * e₂) * ζ⁻¹) := by
          rw [show (Q * τ * Q⁻¹ * τ⁻¹) * (τ * (ζ⁻¹ * (e₁ * e₂))) =
            ((Q * τ * Q⁻¹ * τ⁻¹) * τ) * (ζ⁻¹ * (e₁ * e₂)) by group,
            show (Q * τ * Q⁻¹ * τ⁻¹) * τ = Q * τ * Q⁻¹ by group,
            hζe]

private theorem mul_tau_eq_of_labels (h : Tim79a.ParrottHyp z) {τ q₁ q₂ e₁ e₂ n₁ n₂ : G}
    (hτH : τ ∈ H z) (hτe : ∀ e ∈ centerIn (J z), e * τ = τ * e)
    (hq₁ : q₁ ∈ J z) (hq₂ : q₂ ∈ J z)
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z))
    (hn₁ : n₁ = (q₁ * τ * q₁⁻¹ * τ⁻¹) * e₁) (hn₂ : n₂ = (q₂ * τ * q₂⁻¹ * τ⁻¹) * e₂) :
    ∃ ζ ∈ Subgroup.zpowers z,
      n₁ * n₂ * τ = (q₁ * q₂) * τ * (q₁ * q₂)⁻¹ * (e₁ * e₂ * ζ⁻¹) := by
  set c₁ : G := q₁ * τ * q₁⁻¹ * τ⁻¹ with hc₁
  set c₂ : G := q₂ * τ * q₂⁻¹ * τ⁻¹ with hc₂
  set Q : G := q₁ * q₂ with hQ
  have hc₁J : c₁ ∈ J z := by rw [hc₁]; exact commutator_mul_mem_J hτH hq₁
  have hc₂J : c₂ ∈ J z := by rw [hc₂]; exact commutator_mul_mem_J hτH hq₂
  obtain ⟨ζ, hζz, hζeq⟩ := commutator_mul_tau_exists (z := z) h hτH hq₁ hq₂
  have hζeq' : Q * τ * Q⁻¹ * τ⁻¹ = c₁ * c₂ * ζ := by
    simpa [hQ, hc₁, hc₂] using hζeq
  have hc_eq : c₁ * c₂ = (Q * τ * Q⁻¹ * τ⁻¹) * ζ⁻¹ := by rw [hζeq']; group
  have he₁c₂ : e₁ * c₂ = c₂ * e₁ := (Subgroup.mem_centralizer_iff.mp he₁.2 c₂ hc₂J).symm
  have heτ : e₁ * e₂ * τ = τ * (e₁ * e₂) := by
    rw [show e₁ * e₂ * τ = e₁ * (e₂ * τ) by group, hτe e₂ he₂,
      show e₁ * (τ * e₂) = (e₁ * τ) * e₂ by group, hτe e₁ he₁]
    group
  have hζτ : ζ⁻¹ * τ = τ * ζ⁻¹ := zpowers_z_commute_H h (Subgroup.inv_mem _ hζz) hτH
  have hζe : ζ⁻¹ * (e₁ * e₂) = (e₁ * e₂) * ζ⁻¹ :=
    zpowers_z_commute_H h (Subgroup.inv_mem _ hζz)
      (Subgroup.mul_mem _ (J_le_H he₁.1) (J_le_H he₂.1))
  refine ⟨ζ, hζz, ?_⟩
  rw [hQ, hn₁, hn₂]
  exact mul_tau_calc hc_eq he₁c₂ heτ hζτ hζe

theorem isLemma54Label_mul_tau (h : Tim79a.ParrottHyp z) (P : GL8)
    (_hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (_hσ₂ : orderOf σ₂ = 3) (_hq₂ : qH (z := z) D σ₂ = s2A)
    (_hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (_hτ : τ * τ = 1)
    (_hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (_hτ₂ : τ * σ₂ = σ₂ * τ)
    {n₁ n₂ e₁ e₂ : G} (_hn₁ : n₁ ∈ J z) (_hn₂ : n₂ ∈ J z)
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z))
    (h₁ : IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
      (n₁ * τ) e₁)
    (h₂ : IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
      (n₂ * τ) e₂) :
    IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
        (n₁ * n₂ * τ) (e₁ * e₂) ∨
      IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
        (n₁ * n₂ * τ) (e₁ * e₂ * z) := by
  obtain ⟨q₁, hq₁, hx₁⟩ := h₁
  obtain ⟨q₂, hq₂, hx₂⟩ := h₂
  have hZτ : conjZ z τ = 1 :=
    conjZ_eq_one_of_qH_mem_QP45 (z := z) D h τ (by rw [hqτ]; exact t_mem_Q)
  have hτe : ∀ e ∈ centerIn (J z), e * (τ : G) = (τ : G) * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (centerIn_le_centralizer_of_conjZ_eq_one hZτ he)
  have hn₁ : n₁ = (q₁ * (τ : G) * q₁⁻¹ * (τ : G)⁻¹) * e₁ :=
    eq_commutator_mul_of_label (hτe e₁ he₁) hx₁
  have hn₂ : n₂ = (q₂ * (τ : G) * q₂⁻¹ * (τ : G)⁻¹) * e₂ :=
    eq_commutator_mul_of_label (hτe e₂ he₂) hx₂
  obtain ⟨ζ, hζz, hmain⟩ := mul_tau_eq_of_labels (z := z) h τ.2 hτe hq₁.1 hq₂.1 he₁ he₂ hn₁ hn₂
  have hQ₀ : q₁ * q₂ ∈ J z ⊓
      centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨(J z).mul_mem hq₁.1 hq₂.1, Subgroup.mul_mem _ hq₁.2 hq₂.2⟩
  rcases eq_one_or_eq_z_of_mem_zpowers h (Subgroup.inv_mem _ hζz) with hζ | hζ
  · left
    exact ⟨q₁ * q₂, hQ₀, by rw [hmain, hζ, mul_one]⟩
  · right
    exact ⟨q₁ * q₂, hQ₀, by rw [hmain, hζ]⟩
end CFSG.RankThree.GF2n.Parrott
