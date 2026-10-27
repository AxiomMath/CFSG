module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalWN0

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

@[expose] def lemma54O2 (σ τ : G) : Set G :=
  {n | n ∈ J z ∧ (IsLemma54Label (z := z) σ τ (n * τ) 1 ∨ IsLemma54Label (z := z) σ τ (n * τ) z) ∧
    n ≠ 1 ∧ n ≠ z}

@[expose] def lemma54O3 (σ τ z₁ : G) : Set G :=
  {n | n ∈ J z ∧
    (IsLemma54Label (z := z) σ τ (n * τ) z₁ ∨ IsLemma54Label (z := z) σ τ (n * τ) (z₁ * z)) ∧
    n ≠ z₁ ∧ n ≠ z₁ * z}

private def lemma54O (e₁ e₂ σ τ : G) : Set G :=
  {n | n ∈ J z ∧
    (IsLemma54Label (z := z) σ τ (n * τ) e₁ ∨
      IsLemma54Label (z := z) σ τ (n * τ) e₂) ∧
    n ≠ e₁ ∧ n ≠ e₂}

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private noncomputable def sigma54 (σ₂ : ↥(H z)) : G :=
  ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)

private theorem z_ne_one (h : Tim79a.ParrottHyp z) : z ≠ 1 := by
  intro hz
  have h2 := h.1
  rw [hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem z_mul_self (h : Tim79a.ParrottHyp z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.1, pow_two] at this

private theorem eq_of_mul_z_eq {a b : G} (hz : z * z = 1) (h : a * z = b) :
    a = b * z := by
  calc a = a * z * z := by rw [mul_assoc, hz, mul_one]
    _ = b * z := by rw [h]

private theorem z1_ne_one {z₁ : G} (hz₁z : z₁ ∉ Subgroup.zpowers z) : z₁ ≠ 1 := by
  intro h
  apply hz₁z
  rw [h]
  exact Subgroup.one_mem _

private theorem z1_ne_z {z₁ : G} (hz₁z : z₁ ∉ Subgroup.zpowers z) : z₁ ≠ z := by
  intro h
  apply hz₁z
  rw [h]
  exact Subgroup.mem_zpowers z

private theorem z1_comm_z (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) : z₁ * z = z * z₁ :=
  (Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h)).symm

private theorem z1z_ne_one (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁z : z₁ ∉ Subgroup.zpowers z) : z₁ * z ≠ 1 := by
  intro hz
  apply z1_ne_z hz₁z
  calc z₁ = z₁ * (z * z) := by rw [z_mul_self h, mul_one]
    _ = (z₁ * z) * z := (mul_assoc z₁ z z).symm
    _ = 1 * z := by rw [hz]
    _ = z := one_mul z

private theorem z1z_ne_z (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁z : z₁ ∉ Subgroup.zpowers z) : z₁ * z ≠ z := by
  intro hz
  apply z1_ne_one hz₁z
  calc z₁ = z₁ * (z * z) := by rw [z_mul_self h, mul_one]
    _ = (z₁ * z) * z := (mul_assoc z₁ z z).symm
    _ = z * z := by rw [hz]
    _ = 1 := z_mul_self h

private theorem z1_ne_z1z (h : Tim79a.ParrottHyp z) {z₁ : G} : z₁ ≠ z₁ * z := by
  intro heq
  have hz : z = 1 := by
    have := congrArg (fun x => z₁⁻¹ * x) heq
    simpa [mul_assoc] using this.symm
  exact z_ne_one h hz

private theorem conj_z_eq_self_of_mem_H (h : Tim79a.ParrottHyp z) {c : G} (hc : c ∈ H z) :
    c * z * c⁻¹ = z := by
  have hzc : c * z = z * c :=
    Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) c hc
  calc c * z * c⁻¹ = (c * z) * c⁻¹ := by rw [mul_assoc]
    _ = (z * c) * c⁻¹ := by rw [hzc]
    _ = z := by group

private theorem conj_z1_eq_z1_or_mul (h : Tim79a.ParrottHyp z) {z₁ c : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hcH : c ∈ H z) : c * z₁ * c⁻¹ = z₁ ∨ c * z₁ * c⁻¹ = z₁ * z := by
  by_cases hcC : c ∈ centralizer ({z₁} : Set G)
  · left
    exact Commute.mul_inv_cancel (Subgroup.mem_centralizer_singleton_iff.mp hcC)
  · right
    have hcj := conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hcH hcC
    rwa [← z1_comm_z h hz₁] at hcj

private theorem isLabel_tau_mul (σ τ e : G) :
    IsLemma54Label (z := z) σ τ (τ * e) e := by
  refine ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, ?_⟩
  simp

private theorem isLabel_mul_right {σ τ x e a : G}
    (hx : IsLemma54Label (z := z) σ τ x e) :
    IsLemma54Label (z := z) σ τ (x * a) (e * a) := by
  obtain ⟨q, hq, hx⟩ := hx
  refine ⟨q, hq, ?_⟩
  calc x * a = (q * τ * q⁻¹ * e) * a := by rw [hx]
    _ = q * τ * q⁻¹ * (e * a) := by group

private theorem eq_of_mul_tau_eq_tau_mul {τ e n : G} (hτ : τ * τ = 1)
    (heτ : e * τ = τ * e) (he2 : e * e = 1) (h : n * τ = τ * e) : n = e := by
  calc n = n * τ * τ := by rw [mul_assoc, hτ, mul_one]
    _ = (τ * e) * τ := by rw [h]
    _ = τ * (e * τ) := by rw [mul_assoc]
    _ = τ * (τ * e) := by rw [heτ]
    _ = (τ * τ) * e := by rw [mul_assoc]
    _ = e := by rw [hτ, one_mul]

private theorem eq_tau_mul_of_mul_tau_eq {x e τ : G} (hτ : τ * τ = 1)
    (heτ : e * τ = τ * e) (h : x * τ = e) : x = τ * e := by
  calc x = x * τ * τ := by rw [mul_assoc, hτ, mul_one]
    _ = e * τ := by rw [h]
    _ = τ * e := heτ

private theorem comm_tau_of_mem_centerIn (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G} (ha : a ∈ centerIn (J z)) :
    a * (τ : G) = (τ : G) * a :=
  Subgroup.mem_centralizer_singleton_iff.mp
    ((Subgroup.mem_inf.mp
      (centerIn_J_le_lemma54N (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ ha)).2)

private theorem z_comm_tau (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) :
    z * (τ : G) = (τ : G) * z :=
  comm_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
    (z_mem_centerIn_J h)

private theorem z1_comm_tau (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) :
    z₁ * (τ : G) = (τ : G) * z₁ :=
  comm_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hz₁

private theorem isLabel_mul_tau_of_mem_centerIn (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G} (ha : a ∈ centerIn (J z)) :
    IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
      (a * (τ : G)) a := by
  have hcomm := comm_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ ha
  simpa [hcomm] using
    isLabel_tau_mul (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) a

private theorem tau_not_mem_J {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) :
    (τ : G) ∉ J z := by
  intro hτJ
  have hq : qH (z := z) D ⟨(τ : G), τ.2⟩ = 1 :=
    (J_mem_iff D ⟨(τ : G), τ.2⟩).mp (Subgroup.mem_subgroupOf.mpr hτJ)
  have h1 : tA = (1 : A45) := by
    rw [← hqτ]
    exact hq
  exact t_ne_one (congrArg Subtype.val h1)

private theorem tau_mem_lemma54W (σ τ : G) : τ ∈ lemma54W z σ τ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)

private theorem tau_mul_self_val {τ : ↥(H z)} (hτ : τ * τ = 1) :
    (τ : G) * (τ : G) = 1 := by
  simpa using congrArg Subtype.val hτ

private theorem tau_inv_val {τ : ↥(H z)} (hτ : τ * τ = 1) :
    (τ : G)⁻¹ = (τ : G) :=
  inv_eq_of_mul_eq_one_right (tau_mul_self_val hτ)

private theorem exists_label_tau_of_mem_W_J (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G}
    (haW : a ∈ lemma54W z (sigma54 D σ₂) (τ : G)) (haJ : a ∈ J z) :
    ∃ e ∈ centerIn (J z),
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (a * (τ : G)) e := by
  have hτJ : (τ : G) ∉ J z := tau_not_mem_J (z := z) (D := D) hqτ
  have haτW : a * (τ : G) ∈ lemma54W z (sigma54 D σ₂) (τ : G) :=
    (lemma54W z (sigma54 D σ₂) (τ : G)).mul_mem haW (tau_mem_lemma54W _ _)
  have haτJ : a * (τ : G) ∉ J z := by
    intro hmem
    apply hτJ
    have h : a⁻¹ * (a * (τ : G)) ∈ J z := (J z).mul_mem ((J z).inv_mem haJ) hmem
    simpa [mul_assoc] using h
  exact exists_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    haτW haτJ

private theorem mem_O2_or_O3_of_label (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {σ₂ : ↥(H z)} (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} {a e : G} (haJ : a ∈ J z) (he : e ∈ centerIn (J z))
    (hlab : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (a * (τ : G)) e) :
    a = 1 ∨ a = z ∨ a = z₁ ∨ a = z₁ * z ∨
      a ∈ lemma54O2 (z := z) (sigma54 D σ₂) (τ : G) ∨
      a ∈ lemma54O3 (z := z) (sigma54 D σ₂) (τ : G) z₁ := by
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with he1 | hez | hez1 | hez1z
  · subst e
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · by_cases haz : a = z
      · exact Or.inr (Or.inl haz)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨haJ, Or.inl hlab, ha1, haz⟩))))
  · subst e
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · by_cases haz : a = z
      · exact Or.inr (Or.inl haz)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨haJ, Or.inr hlab, ha1, haz⟩))))
  · subst e
    by_cases hz1a : a = z₁
    · exact Or.inr (Or.inr (Or.inl hz1a))
    · by_cases hz1za : a = z₁ * z
      · exact Or.inr (Or.inr (Or.inr (Or.inl hz1za)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨haJ, Or.inl hlab, hz1a, hz1za⟩))))
  · subst e
    have hlab' : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
        (a * (τ : G)) (z₁ * z) := by
      simpa [← z1_comm_z h hz₁] using hlab
    by_cases hz1a : a = z₁
    · exact Or.inr (Or.inr (Or.inl hz1a))
    · by_cases hz1za : a = z₁ * z
      · exact Or.inr (Or.inr (Or.inr (Or.inl hz1za)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr ⟨haJ, Or.inr hlab', hz1a, hz1za⟩))))

theorem mem_lemma54O2_or_mem_lemma54O3 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {a : G} (haW : a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
    (haJ : a ∈ J z) :
    a = 1 ∨ a = z ∨ a = z₁ ∨ a = z₁ * z ∨
      a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∨
      a ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁ := by
  obtain ⟨e, he, hlab⟩ :=
    exists_label_tau_of_mem_W_J (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ haW haJ
  exact mem_O2_or_O3_of_label (z := z) (D := D) h hz₁ hz₁z hord hc₂ haJ he hlab

theorem mem_lemma54W_of_mem_lemma54O2 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {a : G} (ha : a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) :
    a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∧ a ∈ J z ∧
      a ∉ centerIn (J z) := by
  simp only [lemma54O2, Set.mem_setOf_eq] at ha
  obtain ⟨haJ, hlab, ha1, haz⟩ := ha
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have hτW : (τ : G) ∈ lemma54W z
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
    tau_mem_lemma54W (z := z) _ _
  have haW : a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
    rcases hlab with hlab | hlab
    · have haτW : a * (τ : G) ∈ lemma54W z
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
        (mem_lemma54W_of_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          (Subgroup.one_mem _) hlab).1
      have h := (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        (τ : G)).mul_mem haτW hτW
      simpa [mul_assoc, hτG] using h
    · have haτW : a * (τ : G) ∈ lemma54W z
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
        (mem_lemma54W_of_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          (z_mem_centerIn_J h) hlab).1
      have h := (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        (τ : G)).mul_mem haτW hτW
      simpa [mul_assoc, hτG] using h
  refine ⟨haW, haJ, ?_⟩
  intro haZ
  have hlabela :=
    isLabel_mul_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ haZ
  rcases hlab with hlab | hlab
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (Subgroup.one_mem _) haZ hlab hlabela
    exact ha1 heq.symm
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (z_mem_centerIn_J h) haZ hlab hlabela
    exact haz heq.symm

theorem mem_lemma54W_of_mem_lemma54O3 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {a : G}
    (ha : a ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁) :
    a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∧ a ∈ J z ∧
      a ∉ centerIn (J z) := by
  simp only [lemma54O3, Set.mem_setOf_eq] at ha
  obtain ⟨haJ, hlab, hz1a, hz1za⟩ := ha
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have hτW : (τ : G) ∈ lemma54W z
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
    tau_mem_lemma54W (z := z) _ _
  have hz1z_mem : z₁ * z ∈ centerIn (J z) := (centerIn (J z)).mul_mem hz₁ (z_mem_centerIn_J h)
  have haW : a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) := by
    rcases hlab with hlab | hlab
    · have haτW : a * (τ : G) ∈ lemma54W z
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
        (mem_lemma54W_of_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          hz₁ hlab).1
      have h := (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        (τ : G)).mul_mem haτW hτW
      simpa [mul_assoc, hτG] using h
    · have haτW : a * (τ : G) ∈ lemma54W z
          ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
        (mem_lemma54W_of_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          hz1z_mem hlab).1
      have h := (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
        (τ : G)).mul_mem haτW hτW
      simpa [mul_assoc, hτG] using h
  refine ⟨haW, haJ, ?_⟩
  intro haZ
  have hlabela :=
    isLabel_mul_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ haZ
  rcases hlab with hlab | hlab
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hz₁ haZ hlab hlabela
    exact hz1a heq.symm
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hz1z_mem haZ hlab hlabela
    exact hz1za heq.symm

theorem disjoint_lemma54O2_lemma54O3 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    Disjoint (lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
      (lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁) := by
  rw [Set.disjoint_left]
  intro a ha2 ha3
  simp only [lemma54O2, Set.mem_setOf_eq] at ha2
  simp only [lemma54O3, Set.mem_setOf_eq] at ha3
  obtain ⟨-, hlab2, -⟩ := ha2
  obtain ⟨-, hlab3, -⟩ := ha3
  have hz1z_mem : z₁ * z ∈ centerIn (J z) := (centerIn (J z)).mul_mem hz₁ (z_mem_centerIn_J h)
  rcases hlab2 with h2 | h2 <;> rcases hlab3 with h3 | h3
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (Subgroup.one_mem _) hz₁ h2 h3
    exact z1_ne_one hz₁z heq.symm
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (Subgroup.one_mem _) hz1z_mem h2 h3
    exact z1z_ne_one h hz₁z heq.symm
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (z_mem_centerIn_J h) hz₁ h2 h3
    exact z1_ne_z hz₁z heq.symm
  · have heq := isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (z_mem_centerIn_J h) hz1z_mem h2 h3
    exact z1z_ne_z h hz₁z heq.symm

private theorem ncard_labelPair_union (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {e₁ e₂ : G}
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z)) (he₁₂ : e₁ ≠ e₂) :
    ({y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₁} ∪
      {y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₂}).ncard = 8 := by
  change ({y : G | IsLemma54Label (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) y e₁} ∪
    {y : G | IsLemma54Label (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) y e₂}).ncard = 8
  have hdisj : Disjoint
      {y : G | IsLemma54Label (z := z)
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) y e₁}
      {y : G | IsLemma54Label (z := z)
        ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) y e₂} := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    exact he₁₂ (isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      he₁ he₂ hy₁ hy₂)
  rw [Set.ncard_union_eq hdisj,
    ncard_setOf_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he₁,
    ncard_setOf_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he₂]

private theorem ncard_labelPair_image_mem (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    {e₁ e₂ : G} (he₁τ : e₁ * (τ : G) = (τ : G) * e₁)
    (he₂τ : e₂ * (τ : G) = (τ : G) * e₂) (he₁sq : e₁ * e₁ = 1) (he₂sq : e₂ * e₂ = 1)
    {n : G} (hn : n ∈ lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G)) :
    n * (τ : G) ∈
      ({y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₁} ∪
        {y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₂}) \
      ({(τ : G) * e₁, (τ : G) * e₂} : Set G) := by
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  simp only [lemma54O, sigma54, Set.mem_setOf_eq] at hn
  obtain ⟨-, hlab, hn₁, hn₂⟩ := hn
  simp only [sigma54]
  refine ⟨?_, ?_⟩
  · rcases hlab with hlab | hlab
    · exact Or.inl hlab
    · exact Or.inr hlab
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      exact hn₁ (eq_of_mul_tau_eq_tau_mul hτG he₁τ he₁sq h)
    · intro h
      exact hn₂ (eq_of_mul_tau_eq_tau_mul hτG he₂τ he₂sq h)

private theorem label_of_mem_labelPair {σ τ e₁ e₂ x : G}
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z))
    (hxL : x ∈
      ({y : G | IsLemma54Label (z := z) σ τ y e₁} ∪
        {y : G | IsLemma54Label (z := z) σ τ y e₂})) :
    ∃ e ∈ centerIn (J z),
      IsLemma54Label (z := z) σ τ x e ∧ (e = e₁ ∨ e = e₂) := by
  rcases hxL with hx | hx
  · exact ⟨e₁, he₁, hx, Or.inl rfl⟩
  · exact ⟨e₂, he₂, hx, Or.inr rfl⟩

private theorem ncard_labelPair_preimage_J (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {x e : G}
    (he : e ∈ centerIn (J z))
    (hxlab : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) x e) :
    x * (τ : G) ∈ J z := by
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have hτJ : (τ : G) ∉ J z := tau_not_mem_J (z := z) (D := D) hqτ
  obtain ⟨hxW, hxJ⟩ :=
    mem_lemma54W_of_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      he hxlab
  rcases (mem_lemma54W_iff (z := z) (σ := sigma54 D σ₂) (τ := (τ : G)) hτG).mp hxW
    with hN | hτxN
  · exact absurd hN.1.1 hxJ
  · have h := conj_mem_J_of_mem_H (z := z) (s := (τ : G)) τ.2 hτxN.1.1
    have hconj : (τ : G) * ((τ : G) * x) * (τ : G)⁻¹ = x * (τ : G) := by
      rw [tau_inv_val hτ]
      calc (τ : G) * ((τ : G) * x) * (τ : G) =
          ((τ : G) * (τ : G)) * x * (τ : G) := by group
        _ = x * (τ : G) := by rw [hτG, one_mul]
    rwa [hconj] at h

private theorem ncard_labelPair_preimage_mem (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} {τ : ↥(H z)} (hτ : τ * τ = 1) {e₁ e₂ x e : G}
    (hepair : e = e₁ ∨ e = e₂) (hxlab : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) x e)
    (hxpair : x ∉ ({(τ : G) * e₁, (τ : G) * e₂} : Set G))
    (he₁τ : e₁ * (τ : G) = (τ : G) * e₁) (he₂τ : e₂ * (τ : G) = (τ : G) * e₂)
    (hxτJ : x * (τ : G) ∈ J z) :
    x * (τ : G) ∈ lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G) := by
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  simp only [lemma54O, Set.mem_setOf_eq]
  refine ⟨hxτJ, ?_, ?_, ?_⟩
  · have hlab : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
        (x * (τ : G) * (τ : G)) e := by
      rwa [show x * (τ : G) * (τ : G) = x by rw [mul_assoc, hτG, mul_one]]
    rcases hepair with rfl | rfl
    · left; exact hlab
    · right; exact hlab
  · intro hb
    apply hxpair
    have hxeq : x = (τ : G) * e₁ := eq_tau_mul_of_mul_tau_eq hτG he₁τ hb
    rw [hxeq]; simp
  · intro hb
    apply hxpair
    have hxeq : x = (τ : G) * e₂ := eq_tau_mul_of_mul_tau_eq hτG he₂τ hb
    rw [hxeq]; simp

private theorem ncard_labelPair_preimage (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {e₁ e₂ : G}
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z))
    (he₁τ : e₁ * (τ : G) = (τ : G) * e₁) (he₂τ : e₂ * (τ : G) = (τ : G) * e₂)
    {x : G}
    (hx : x ∈
      ({y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₁} ∪
        {y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₂}) \
      ({(τ : G) * e₁, (τ : G) * e₂} : Set G)) :
    ∃ n, n ∈ lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G) ∧ n * (τ : G) = x := by
  simp only [sigma54] at hx ⊢
  obtain ⟨hxL, hxpair⟩ := hx
  obtain ⟨e, he, hxlab, hepair⟩ :=
    label_of_mem_labelPair (z := z)
      (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (τ := (τ : G)) he₁ he₂
      (by simpa using hxL)
  have hxτJ : x * (τ : G) ∈ J z :=
    ncard_labelPair_preimage_J (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he hxlab
  refine ⟨x * (τ : G),
    ncard_labelPair_preimage_mem (z := z) (D := D) (σ₂ := σ₂) h hτ hepair hxlab
      (by simpa using hxpair) he₁τ he₂τ hxτJ, ?_⟩
  rw [mul_assoc, tau_mul_self_val hτ, mul_one]

private theorem ncard_labelPair_congr (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {e₁ e₂ : G}
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z))
    (he₁τ : e₁ * (τ : G) = (τ : G) * e₁) (he₂τ : e₂ * (τ : G) = (τ : G) * e₂) :
    (lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G)).ncard =
      (({y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₁} ∪
        {y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₂}) \
      ({(τ : G) * e₁, (τ : G) * e₂} : Set G)).ncard := by
  simp only [sigma54]
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have he₁sq : e₁ * e₁ = 1 := centerIn_J_sq h he₁
  have he₂sq : e₂ * e₂ = 1 := centerIn_J_sq h he₂
  refine Set.ncard_congr (s := lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G))
    (t := (({y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₁} ∪
      {y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₂}) \
      ({(τ : G) * e₁, (τ : G) * e₂} : Set G))) (fun n _ => n * (τ : G)) ?_ ?_ ?_
  · intro n hn
    exact ncard_labelPair_image_mem (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ
      he₁τ he₂τ he₁sq he₂sq hn
  · intro n₁ n₂ _ _ h
    calc n₁ = n₁ * (τ : G) * (τ : G) := by rw [mul_assoc, hτG, mul_one]
      _ = n₂ * (τ : G) * (τ : G) := by rw [h]
      _ = n₂ := by rw [mul_assoc, hτG, mul_one]
  · intro x hx
    obtain ⟨n, hn, hnx⟩ := ncard_labelPair_preimage (z := z) (D := D) h P hP hσ₂ hq₂ hc₂
      hqτ hτ hτ₁ hτ₂ he₁ he₂ he₁τ he₂τ hx
    exact ⟨n, hn, hnx⟩

private theorem ncard_labelPair (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {e₁ e₂ : G}
    (he₁ : e₁ ∈ centerIn (J z)) (he₂ : e₂ ∈ centerIn (J z)) (he₁₂ : e₁ ≠ e₂) :
    (lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G)).ncard = 6 := by
  have he₁τ : e₁ * (τ : G) = (τ : G) * e₁ :=
    comm_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ he₁
  have he₂τ : e₂ * (τ : G) = (τ : G) * e₂ :=
    comm_tau_of_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ he₂
  rw [ncard_labelPair_congr (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    he₁ he₂ he₁τ he₂τ]
  have hpairsub : ({(τ : G) * e₁, (τ : G) * e₂} : Set G) ⊆
      ({y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₁} ∪
        {y : G | IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) y e₂}) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_union_left _ (isLabel_tau_mul (z := z) (sigma54 D σ₂) (τ : G) e₁)
    · exact Set.mem_union_right _ (isLabel_tau_mul (z := z) (sigma54 D σ₂) (τ : G) e₂)
  have hpairne : (τ : G) * e₁ ≠ (τ : G) * e₂ := by
    intro h
    exact he₁₂ (mul_left_cancel h)
  rw [Set.ncard_sdiff hpairsub, Set.ncard_pair hpairne,
    ncard_labelPair_union (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      he₁ he₂ he₁₂]

theorem ncard_lemma54O2 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).ncard = 6 := by
  simpa only [lemma54O2, lemma54O, sigma54] using
    (ncard_labelPair (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (e₁ := 1) (e₂ := z) (Subgroup.one_mem _) (z_mem_centerIn_J h) (z_ne_one h).symm)

theorem ncard_lemma54O3 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁).ncard = 6 := by
  simpa only [lemma54O3, lemma54O, sigma54] using
    (ncard_labelPair (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (e₁ := z₁) (e₂ := z₁ * z) hz₁
      ((centerIn (J z)).mul_mem hz₁ (z_mem_centerIn_J h)) (z1_ne_z1z h))

private theorem mul_z_mem_O2 (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G}
    (ha : a ∈ lemma54O2 (z := z) (sigma54 D σ₂) (τ : G)) :
    a * z ∈ lemma54O2 (z := z) (sigma54 D σ₂) (τ : G) := by
  simp only [lemma54O2, Set.mem_setOf_eq] at ha
  obtain ⟨haJ, hlab, ha1, haz⟩ := ha
  have hz2 : z * z = 1 := z_mul_self h
  have hzτ : z * (τ : G) = (τ : G) * z :=
    z_comm_tau (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
  refine ⟨(J z).mul_mem haJ (z_mem_J h), ?_, ?_, ?_⟩
  · rcases hlab with hlab | hlab
    · right
      have h := isLabel_mul_right (z := z) (σ := sigma54 D σ₂) (τ := (τ : G))
        (x := a * (τ : G)) (e := 1) (a := z) hlab
      rw [show (a * (τ : G)) * z = (a * z) * (τ : G) by
        rw [mul_assoc, ← hzτ, ← mul_assoc]] at h
      simpa using h
    · left
      have h := isLabel_mul_right (z := z) (σ := sigma54 D σ₂) (τ := (τ : G))
        (x := a * (τ : G)) (e := z) (a := z) hlab
      rw [show (a * (τ : G)) * z = (a * z) * (τ : G) by
        rw [mul_assoc, ← hzτ, ← mul_assoc]] at h
      simpa [hz2] using h
  · intro hb
    exact haz (by simpa using eq_of_mul_z_eq (z := z) hz2 hb)
  · intro hb
    exact ha1 (by simpa [hz2] using eq_of_mul_z_eq (z := z) hz2 hb)

private theorem mul_z_mem_O3 (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a z₁ : G}
    (ha : a ∈ lemma54O3 (z := z) (sigma54 D σ₂) (τ : G) z₁) :
    a * z ∈ lemma54O3 (z := z) (sigma54 D σ₂) (τ : G) z₁ := by
  simp only [lemma54O3, Set.mem_setOf_eq] at ha
  obtain ⟨haJ, hlab, hz1a, hz1za⟩ := ha
  have hz2 : z * z = 1 := z_mul_self h
  have hzτ : z * (τ : G) = (τ : G) * z :=
    z_comm_tau (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
  refine ⟨(J z).mul_mem haJ (z_mem_J h), ?_, ?_, ?_⟩
  · rcases hlab with hlab | hlab
    · right
      have h := isLabel_mul_right (z := z) (σ := sigma54 D σ₂) (τ := (τ : G))
        (x := a * (τ : G)) (e := z₁) (a := z) hlab
      rw [show (a * (τ : G)) * z = (a * z) * (τ : G) by
        rw [mul_assoc, ← hzτ, ← mul_assoc]] at h
      simpa using h
    · left
      have h := isLabel_mul_right (z := z) (σ := sigma54 D σ₂) (τ := (τ : G))
        (x := a * (τ : G)) (e := z₁ * z) (a := z) hlab
      rw [show (a * (τ : G)) * z = (a * z) * (τ : G) by
        rw [mul_assoc, ← hzτ, ← mul_assoc]] at h
      simpa [mul_assoc, hz2] using h
  · intro hb
    exact hz1za (by simpa using eq_of_mul_z_eq (z := z) hz2 hb)
  · intro hb
    exact hz1a (by simpa [mul_assoc, hz2] using eq_of_mul_z_eq (z := z) hz2 hb)

theorem mul_z_mem_lemma54O2 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (∀ a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
        a * z ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) ∧
      ∀ a ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁,
        a * z ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁ := by
  exact ⟨fun a ha => mul_z_mem_O2 (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha,
    fun a ha => mul_z_mem_O3 (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ ha⟩

private theorem exists_label_conj_tau (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G)) :
    ∃ ℓ m, ℓ ∈ centerIn (J z) ∧
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (c * (τ : G) * c⁻¹) ℓ ∧
      m ∈ J z ∧ m * (τ : G) = c * (τ : G) * c⁻¹ ∧
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (m * (τ : G)) ℓ := by
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have hτJ : (τ : G) ∉ J z := tau_not_mem_J (z := z) (D := D) hqτ
  obtain ⟨hc1, hcH⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hcW, -⟩ := Subgroup.mem_inf.mp hc1
  have hτW : (τ : G) ∈ lemma54W z (sigma54 D σ₂) (τ : G) := tau_mem_lemma54W _ _
  have hcτW : c * (τ : G) * c⁻¹ ∈ lemma54W z (sigma54 D σ₂) (τ : G) :=
    (Subgroup.mem_normalizer_iff.mp hcW (τ : G)).mp hτW
  have hcτJ : c * (τ : G) * c⁻¹ ∉ J z := by
    intro hJ
    apply hτJ
    have hcInvH : c⁻¹ ∈ H z := (H z).inv_mem hcH
    have h := conj_mem_J_of_mem_H (z := z) hcInvH hJ
    rwa [show c⁻¹ * (c * (τ : G) * c⁻¹) * (c⁻¹)⁻¹ = (τ : G) by group] at h
  obtain ⟨ℓ, hℓZ, hℓ⟩ :=
    exists_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hcτW hcτJ
  let m : G := (c * (τ : G) * c⁻¹) * (τ : G)
  have hm_eq : m = (τ : G) * (c * (τ : G) * c⁻¹) :=
    lemma54W_comm (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (c * (τ : G) * c⁻¹) hcτW (τ : G) hτW
  have hmJ : m ∈ J z := by
    rw [hm_eq]
    rcases (mem_lemma54W_iff (z := z) (σ := sigma54 D σ₂) (τ := (τ : G)) hτG).mp
      hcτW with hN | hτxN
    · exact absurd hN.1.1 hcτJ
    · exact hτxN.1.1
  have hmτ : m * (τ : G) = c * (τ : G) * c⁻¹ := by
    show ((c * (τ : G) * c⁻¹) * (τ : G)) * (τ : G) = c * (τ : G) * c⁻¹
    rw [mul_assoc, hτG, mul_one]
  have hℓm : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (m * (τ : G)) ℓ := by
    rwa [hmτ]
  exact ⟨ℓ, m, hℓZ, hℓ, hmJ, hmτ, hℓm⟩

private theorem exists_label_conj_b (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G)) (haJ : a ∈ J z)
    (haτW : a * (τ : G) ∈ lemma54W z (sigma54 D σ₂) (τ : G)) :
    ∃ f ∈ centerIn (J z),
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) ((c * a * c⁻¹) * (τ : G)) f := by
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have hτJ : (τ : G) ∉ J z := tau_not_mem_J (z := z) (D := D) hqτ
  obtain ⟨hc1, hcH⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨hcW, -⟩ := Subgroup.mem_inf.mp hc1
  have hτW : (τ : G) ∈ lemma54W z (sigma54 D σ₂) (τ : G) := tau_mem_lemma54W _ _
  have hcaτW : c * (a * (τ : G)) * c⁻¹ ∈ lemma54W z (sigma54 D σ₂) (τ : G) :=
    (Subgroup.mem_normalizer_iff.mp hcW (a * (τ : G))).mp haτW
  have hcτW : c * (τ : G) * c⁻¹ ∈ lemma54W z (sigma54 D σ₂) (τ : G) :=
    (Subgroup.mem_normalizer_iff.mp hcW (τ : G)).mp hτW
  have hbJ : c * a * c⁻¹ ∈ J z := conj_mem_J_of_mem_H (z := z) hcH haJ
  have hbW : c * a * c⁻¹ ∈ lemma54W z (sigma54 D σ₂) (τ : G) := by
    have h := (lemma54W z (sigma54 D σ₂) (τ : G)).mul_mem hcaτW
      ((lemma54W z (sigma54 D σ₂) (τ : G)).inv_mem hcτW)
    rwa [show c * (a * (τ : G)) * c⁻¹ * (c * (τ : G) * c⁻¹)⁻¹ = c * a * c⁻¹ by
      group] at h
  have hbτW : (c * a * c⁻¹) * (τ : G) ∈ lemma54W z (sigma54 D σ₂) (τ : G) :=
    (lemma54W z (sigma54 D σ₂) (τ : G)).mul_mem hbW hτW
  have hbτJ : (c * a * c⁻¹) * (τ : G) ∉ J z := by
    intro hJ
    apply hτJ
    have hmem : (c * a * c⁻¹)⁻¹ * ((c * a * c⁻¹) * (τ : G)) ∈ J z :=
      (J z).mul_mem ((J z).inv_mem hbJ) hJ
    simpa [mul_assoc] using hmem
  exact exists_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    hbτW hbτJ

private theorem exists_label_conj_f (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a ℓ m : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G)) (haJ : a ∈ J z)
    (haτW : a * (τ : G) ∈ lemma54W z (sigma54 D σ₂) (τ : G))
    (hℓZ : ℓ ∈ centerIn (J z))
    (hmJ : m ∈ J z) (hmτ : m * (τ : G) = c * (τ : G) * c⁻¹)
    (hℓm : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (m * (τ : G)) ℓ) :
    ∃ f ∈ centerIn (J z),
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) ((c * a * c⁻¹) * (τ : G)) f ∧
      (IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
          (c * (a * (τ : G)) * c⁻¹) (f * ℓ) ∨
        IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
          (c * (a * (τ : G)) * c⁻¹) (f * ℓ * z)) := by
  have hbJ : c * a * c⁻¹ ∈ J z := conj_mem_J_of_mem_H (z := z) (Subgroup.mem_inf.mp hc).2 haJ
  obtain ⟨f, hfZ, hf⟩ :=
    exists_label_conj_b (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hc haJ haτW
  have hmul := isLemma54Label_mul_tau (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    hbJ hmJ hfZ hℓZ hf hℓm
  have hxeq : ((c * a * c⁻¹) * m) * (τ : G) = c * (a * (τ : G)) * c⁻¹ := by
    calc ((c * a * c⁻¹) * m) * (τ : G) = (c * a * c⁻¹) * (m * (τ : G)) := by
          rw [mul_assoc]
      _ = (c * a * c⁻¹) * (c * (τ : G) * c⁻¹) := by rw [hmτ]
      _ = c * (a * (τ : G)) * c⁻¹ := by group
  refine ⟨f, hfZ, hf, ?_⟩
  rcases hmul with hmul | hmul
  · left
    rwa [hxeq] at hmul
  · right
    rwa [hxeq] at hmul

private theorem eq_or_of_center_mul {ℓ f A : G} (hℓ2 : ℓ * ℓ = 1) (hℓf : ℓ * f = f * ℓ)
    (hEq : ℓ * A = f * ℓ ∨ ℓ * A = f * ℓ * z) : A = f ∨ A = f * z := by
  rcases hEq with hEq | hEq
  · left
    calc A = ℓ * (ℓ * A) := by rw [← mul_assoc, hℓ2, one_mul]
      _ = ℓ * (f * ℓ) := by rw [hEq]
      _ = (ℓ * f) * ℓ := by group
      _ = (f * ℓ) * ℓ := by rw [hℓf]
      _ = f := by rw [mul_assoc, hℓ2, mul_one]
  · right
    calc A = ℓ * (ℓ * A) := by rw [← mul_assoc, hℓ2, one_mul]
      _ = ℓ * (f * ℓ * z) := by rw [hEq]
      _ = f * z := by
          calc ℓ * (f * ℓ * z) = (ℓ * f) * (ℓ * z) := by group
            _ = (f * ℓ) * (ℓ * z) := by rw [hℓf]
            _ = f * (ℓ * ℓ) * z := by group
            _ = f * z := by rw [hℓ2, mul_one]

private theorem label_conj_eq_or_mul (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a e ℓ f : G}
    (hcH : c ∈ H z)
    (he : e ∈ centerIn (J z)) (hℓZ : ℓ ∈ centerIn (J z)) (hfZ : f ∈ centerIn (J z))
    (hconj : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
      (c * (a * (τ : G)) * c⁻¹) (ℓ * (c * e * c⁻¹)))
    (hmul : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
        (c * (a * (τ : G)) * c⁻¹) (f * ℓ) ∨
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
        (c * (a * (τ : G)) * c⁻¹) (f * ℓ * z)) :
    ℓ * (c * e * c⁻¹) = f * ℓ ∨ ℓ * (c * e * c⁻¹) = f * ℓ * z := by
  have hHN : H z ≤ Subgroup.normalizer (centerIn (J z) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centerIn_le_H (z := z))).mp
      (centerIn_subgroupOf_normal z)
  have hceZ : c * e * c⁻¹ ∈ centerIn (J z) :=
    (Subgroup.mem_normalizer_iff.mp (hHN hcH) e).mp he
  have hA_Z : ℓ * (c * e * c⁻¹) ∈ centerIn (J z) :=
    (centerIn (J z)).mul_mem hℓZ hceZ
  have hfl_Z : f * ℓ ∈ centerIn (J z) := (centerIn (J z)).mul_mem hfZ hℓZ
  have hflz_Z : f * ℓ * z ∈ centerIn (J z) :=
    (centerIn (J z)).mul_mem hfl_Z (z_mem_centerIn_J h)
  rcases hmul with hmul | hmul
  · left
    exact isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hA_Z hfl_Z hconj hmul
  · right
    exact isLemma54Label_unique (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hA_Z hflz_Z hconj hmul

private theorem label_conj_eq_or (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a e ℓ f : G}
    (hcH : c ∈ H z) (he : e ∈ centerIn (J z)) (hℓZ : ℓ ∈ centerIn (J z))
    (hfZ : f ∈ centerIn (J z))
    (hconj : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
      (c * (a * (τ : G)) * c⁻¹) (ℓ * (c * e * c⁻¹)))
    (hmul : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
        (c * (a * (τ : G)) * c⁻¹) (f * ℓ) ∨
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G)
        (c * (a * (τ : G)) * c⁻¹) (f * ℓ * z)) :
    c * e * c⁻¹ = f ∨ c * e * c⁻¹ = f * z := by
  have hℓ2 : ℓ * ℓ = 1 := centerIn_J_sq h hℓZ
  have hℓf : ℓ * f = f * ℓ :=
    (Subgroup.mem_centralizer_iff.mp hℓZ.2 f hfZ.1).symm
  exact eq_or_of_center_mul hℓ2 hℓf
    (label_conj_eq_or_mul (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hcH he hℓZ hfZ hconj hmul)

private theorem exists_label_conj (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a e : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G))
    (haJ : a ∈ J z) (he : e ∈ centerIn (J z))
    (hlab : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (a * (τ : G)) e) :
    ∃ f ∈ centerIn (J z),
      (f = c * e * c⁻¹ ∨ f = (c * e * c⁻¹) * z) ∧
      IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) ((c * a * c⁻¹) * (τ : G)) f := by
  obtain ⟨hc1, hcH⟩ := Subgroup.mem_inf.mp hc
  obtain ⟨-, hcσ⟩ := Subgroup.mem_inf.mp hc1
  obtain ⟨haτW, -⟩ :=
    mem_lemma54W_of_isLemma54Label (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he hlab
  obtain ⟨ℓ, m, hℓZ, hℓ, hmJ, hmτ, hℓm⟩ :=
    exists_label_conj_tau (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hc
  obtain ⟨f, hfZ, hf, hmul⟩ :=
    exists_label_conj_f (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hc haJ haτW
      hℓZ hmJ hmτ hℓm
  have hconj := isLemma54Label_conj (z := z) hcH hcσ hℓZ hℓ hlab
  have hA_or := label_conj_eq_or (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    hcH he hℓZ hfZ hconj hmul
  refine ⟨f, hfZ, ?_, hf⟩
  rcases hA_or with hAf | hAfz
  · exact Or.inl hAf.symm
  · right
    calc f = f * z * z := by rw [mul_assoc, z_mul_self h, mul_one]
      _ = (c * e * c⁻¹) * z := by rw [← hAfz]

private theorem mem_pair_of_conj_label {e₁ e₂ f A : G}
    (hfor : f = A ∨ f = A * z) (hA : A = e₁ ∨ A = e₂)
    (hz₁ : e₁ * z = e₂) (hz₂ : e₂ * z = e₁) : f = e₁ ∨ f = e₂ := by
  rcases hfor with hf | hf
  · rw [hf]; exact hA
  · rw [hf]
    rcases hA with hA | hA
    · rw [hA, hz₁]; right; rfl
    · rw [hA, hz₂]; left; rfl

private theorem ne_pair_of_conj {c a e₁ e₂ : G}
    (hci₁ : c⁻¹ * e₁ * c = e₁ ∨ c⁻¹ * e₁ * c = e₂)
    (hci₂ : c⁻¹ * e₂ * c = e₁ ∨ c⁻¹ * e₂ * c = e₂)
    (ha₁ : a ≠ e₁) (ha₂ : a ≠ e₂) :
    c * a * c⁻¹ ≠ e₁ ∧ c * a * c⁻¹ ≠ e₂ := by
  constructor
  · intro hb
    rcases hci₁ with hci | hci
    · exact ha₁ (by
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = c⁻¹ * e₁ * c := by rw [hb]
          _ = e₁ := hci)
    · exact ha₂ (by
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = c⁻¹ * e₁ * c := by rw [hb]
          _ = e₂ := hci)
  · intro hb
    rcases hci₂ with hci | hci
    · exact ha₁ (by
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = c⁻¹ * e₂ * c := by rw [hb]
          _ = e₁ := hci)
    · exact ha₂ (by
        calc a = c⁻¹ * (c * a * c⁻¹) * c := by group
          _ = c⁻¹ * e₂ * c := by rw [hb]
          _ = e₂ := hci)

private theorem mem_labelPair_of_conj (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a e e₁ e₂ : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G))
    (haJ : a ∈ J z) (ha₁ : a ≠ e₁) (ha₂ : a ≠ e₂)
    (he : e ∈ centerIn (J z))
    (hlab : IsLemma54Label (z := z) (sigma54 D σ₂) (τ : G) (a * (τ : G)) e)
    (he_pair : e = e₁ ∨ e = e₂)
    (hce₁ : c * e₁ * c⁻¹ = e₁ ∨ c * e₁ * c⁻¹ = e₂)
    (hce₂ : c * e₂ * c⁻¹ = e₁ ∨ c * e₂ * c⁻¹ = e₂)
    (hci₁ : c⁻¹ * e₁ * c = e₁ ∨ c⁻¹ * e₁ * c = e₂)
    (hci₂ : c⁻¹ * e₂ * c = e₁ ∨ c⁻¹ * e₂ * c = e₂)
    (hz₁ : e₁ * z = e₂) (hz₂ : e₂ * z = e₁) :
    c * a * c⁻¹ ∈ lemma54O (z := z) e₁ e₂ (sigma54 D σ₂) (τ : G) := by
  obtain ⟨f, hfZ, hfor, hf⟩ :=
    exists_label_conj (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hc haJ he hlab
  have hA : c * e * c⁻¹ = e₁ ∨ c * e * c⁻¹ = e₂ := by
    rcases he_pair with rfl | rfl
    · exact hce₁
    · exact hce₂
  have hf_pair : f = e₁ ∨ f = e₂ := mem_pair_of_conj_label hfor hA hz₁ hz₂
  have hbJ : c * a * c⁻¹ ∈ J z := by
    obtain ⟨hc1, hcH⟩ := Subgroup.mem_inf.mp hc
    exact conj_mem_J_of_mem_H (z := z) hcH haJ
  have hbne := ne_pair_of_conj hci₁ hci₂ ha₁ ha₂
  refine ⟨hbJ, ?_, hbne.1, hbne.2⟩
  rcases hf_pair with hf1 | hf2
  · left; rwa [hf1] at hf
  · right; rwa [hf2] at hf

private theorem mem_O2_of_conj (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G))
    (ha : a ∈ lemma54O2 (z := z) (sigma54 D σ₂) (τ : G)) :
    c * a * c⁻¹ ∈ lemma54O2 (z := z) (sigma54 D σ₂) (τ : G) := by
  simpa only [lemma54O2, lemma54O] using
    (by
      have ha' : a ∈ lemma54O (z := z) 1 z (sigma54 D σ₂) (τ : G) := by
        simpa only [lemma54O2, lemma54O] using ha
      obtain ⟨haJ, hlab, ha1, haz⟩ := by
        simpa only [lemma54O, Set.mem_setOf_eq] using ha'
      obtain ⟨hc1, hcH⟩ := Subgroup.mem_inf.mp hc
      have hz2 : z * z = 1 := z_mul_self h
      have hcz : c * z * c⁻¹ = z := conj_z_eq_self_of_mem_H h hcH
      have hci1 : c⁻¹ * (1 : G) * c = 1 := by group
      have hci2 : c⁻¹ * z * c = z := by simpa using conj_z_eq_self_of_mem_H h ((H z).inv_mem hcH)
      rcases hlab with hlab | hlab
      · exact mem_labelPair_of_conj (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          hc haJ ha1 haz (Subgroup.one_mem _) hlab (Or.inl rfl) (Or.inl (by group))
          (Or.inr hcz) (Or.inl hci1) (Or.inr hci2) (by rw [one_mul]) hz2
      · exact mem_labelPair_of_conj (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          hc haJ ha1 haz (z_mem_centerIn_J h) hlab (Or.inr rfl) (Or.inl (by group))
          (Or.inr hcz) (Or.inl hci1) (Or.inr hci2) (by rw [one_mul]) hz2)

private theorem conj_z1_pair (h : Tim79a.ParrottHyp z) {z₁ c : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hcH : c ∈ H z) :
    (c * z₁ * c⁻¹ = z₁ ∨ c * z₁ * c⁻¹ = z₁ * z) ∧
      (c * (z₁ * z) * c⁻¹ = z₁ ∨ c * (z₁ * z) * c⁻¹ = z₁ * z) ∧
      (c⁻¹ * z₁ * c = z₁ ∨ c⁻¹ * z₁ * c = z₁ * z) ∧
      (c⁻¹ * (z₁ * z) * c = z₁ ∨ c⁻¹ * (z₁ * z) * c = z₁ * z) := by
  have hz2 : z * z = 1 := z_mul_self h
  have hce1 := conj_z1_eq_z1_or_mul h hz₁ hz₁z hord hcH
  have hci1 : c⁻¹ * z₁ * c = z₁ ∨ c⁻¹ * z₁ * c = z₁ * z := by
    simpa using conj_z1_eq_z1_or_mul h hz₁ hz₁z hord ((H z).inv_mem hcH)
  have hcz : c * z * c⁻¹ = z := conj_z_eq_self_of_mem_H h hcH
  have hciz : c⁻¹ * z * c = z := by
    simpa using conj_z_eq_self_of_mem_H h ((H z).inv_mem hcH)
  have hce2 : c * (z₁ * z) * c⁻¹ = z₁ ∨ c * (z₁ * z) * c⁻¹ = z₁ * z := by
    rcases hce1 with hce1 | hce1
    · right
      calc c * (z₁ * z) * c⁻¹ = (c * z₁ * c⁻¹) * (c * z * c⁻¹) := by group
        _ = z₁ * z := by rw [hce1, hcz]
    · left
      calc c * (z₁ * z) * c⁻¹ = (c * z₁ * c⁻¹) * (c * z * c⁻¹) := by group
        _ = (z₁ * z) * z := by rw [hce1, hcz]
        _ = z₁ := by rw [mul_assoc, hz2, mul_one]
  have hci2 : c⁻¹ * (z₁ * z) * c = z₁ ∨ c⁻¹ * (z₁ * z) * c = z₁ * z := by
    rcases hci1 with hci1 | hci1
    · right
      calc c⁻¹ * (z₁ * z) * c = (c⁻¹ * z₁ * c) * (c⁻¹ * z * c) := by group
        _ = z₁ * z := by rw [hci1, hciz]
    · left
      calc c⁻¹ * (z₁ * z) * c = (c⁻¹ * z₁ * c) * (c⁻¹ * z * c) := by group
        _ = (z₁ * z) * z := by rw [hci1, hciz]
        _ = z₁ := by rw [mul_assoc, hz2, mul_one]
  exact ⟨hce1, hce2, hci1, hci2⟩

private theorem mem_O3_of_conj (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {c a : G}
    (hc : c ∈ lemma54N₀ (z := z) (sigma54 D σ₂) (τ : G))
    (ha : a ∈ lemma54O3 (z := z) (sigma54 D σ₂) (τ : G) z₁) :
    c * a * c⁻¹ ∈ lemma54O3 (z := z) (sigma54 D σ₂) (τ : G) z₁ := by
  simpa only [lemma54O3, lemma54O] using
    (by
      have ha' : a ∈ lemma54O (z := z) z₁ (z₁ * z) (sigma54 D σ₂) (τ : G) := by
        simpa only [lemma54O3, lemma54O] using ha
      obtain ⟨haJ, hlab, hz1a, hz1za⟩ := by
        simpa only [lemma54O, Set.mem_setOf_eq] using ha'
      obtain ⟨hc1, hcH⟩ := Subgroup.mem_inf.mp hc
      obtain ⟨hce1, hce2, hci1, hci2⟩ :=
        conj_z1_pair (z := z) h hz₁ hz₁z hord hcH
      have hz2 : z * z = 1 := z_mul_self h
      have hz1e : z₁ * z = z₁ * z := rfl
      have hz2e : (z₁ * z) * z = z₁ := by rw [mul_assoc, hz2, mul_one]
      rcases hlab with hlab | hlab
      · exact mem_labelPair_of_conj (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          hc haJ hz1a hz1za hz₁ hlab (Or.inl rfl) hce1 hce2 hci1 hci2 hz1e hz2e
      · exact mem_labelPair_of_conj (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
          hc haJ hz1a hz1za ((centerIn (J z)).mul_mem hz₁ (z_mem_centerIn_J h)) hlab
          (Or.inr rfl) hce1 hce2 hci1 hci2 hz1e hz2e)

theorem conj_mem_lemma54O2 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {c : G}
    (hc : c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) :
    (∀ a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
        c * a * c⁻¹ ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) ∧
      ∀ a ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁,
        c * a * c⁻¹ ∈
          lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁ := by
  exact ⟨fun a ha => mem_O2_of_conj (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hc ha,
    fun a ha => mem_O3_of_conj (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ
      hτ₁ hτ₂ hc ha⟩

private theorem mem_J_of_mem_O2 {σ τ : G} {a : G}
    (ha : a ∈ lemma54O2 (z := z) σ τ) : a ∈ J z := by
  simp only [lemma54O2, Set.mem_setOf_eq] at ha
  exact ha.1

private theorem mem_J_of_mem_O3 {σ τ z₁ a : G}
    (ha : a ∈ lemma54O3 (z := z) σ τ z₁) : a ∈ J z := by
  simp only [lemma54O3, Set.mem_setOf_eq] at ha
  exact ha.1

private def SixDistinct (z : G) (a g gi : G) : Prop :=
  a ≠ a * z ∧ a ≠ g ∧ a ≠ g * z ∧ a ≠ gi ∧ a ≠ gi * z ∧
  a * z ≠ g ∧ a * z ≠ g * z ∧ a * z ≠ gi ∧ a * z ≠ gi * z ∧
  g ≠ g * z ∧ g ≠ gi ∧ g ≠ gi * z ∧ g * z ≠ gi ∧ g * z ≠ gi * z ∧
  gi ≠ gi * z

private noncomputable def sixFun (z : G) (a g gi : G) : Fin 6 → G :=
  ![a, a * z, g, g * z, gi, gi * z]

private theorem six_injective {a g gi : G} (h : SixDistinct z a g gi) :
    Function.Injective (sixFun z a g gi) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have hz : z ≠ 1 := by
    intro hz1
    exact h1 (by rw [hz1, mul_one])
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [sixFun] at hij ⊢ <;>
    first
    | rfl
    | exact h1 hij
    | exact h1 hij.symm
    | exact h2 hij
    | exact h2 hij.symm
    | exact h3 hij
    | exact h3 hij.symm
    | exact h4 hij
    | exact h4 hij.symm
    | exact h5 hij
    | exact h5 hij.symm
    | exact h6 hij
    | exact h6 hij.symm
    | exact h7 hij
    | exact h7 hij.symm
    | exact h8 hij
    | exact h8 hij.symm
    | exact h9 hij
    | exact h9 hij.symm
    | exact h10 hij
    | exact h10 hij.symm
    | exact h11 hij
    | exact h11 hij.symm
    | exact h12 hij
    | exact h12 hij.symm
    | exact h13 hij
    | exact h13 hij.symm
    | exact h14 hij
    | exact h14 hij.symm
    | exact h15 hij
    | exact h15 hij.symm
    | exact hz hij
    | exact hz hij.symm

private theorem six_ncard {a g gi : G} (h : SixDistinct z a g gi) :
    (Set.range (sixFun z a g gi)).ncard = 6 := by
  rw [Set.ncard_range_of_injective (six_injective h)]
  simp

private theorem six_eq_range {X : Set G} {a g gi : G} (h : SixDistinct z a g gi)
    (ha : a ∈ X) (haz : a * z ∈ X) (hg : g ∈ X) (hgz : g * z ∈ X)
    (hgi : gi ∈ X) (hgiz : gi * z ∈ X) (hXcard : X.ncard = 6) :
    X = Set.range (sixFun z a g gi) := by
  have hS_ncard : (Set.range (sixFun z a g gi)).ncard = 6 := six_ncard h
  have hsub : Set.range (sixFun z a g gi) ⊆ X := by
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa [sixFun] using ha
    · simpa [sixFun] using haz
    · simpa [sixFun] using hg
    · simpa [sixFun] using hgz
    · simpa [sixFun] using hgi
    · simpa [sixFun] using hgiz
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hXcard, hS_ncard])).symm

private theorem six_ineq (h : Tim79a.ParrottHyp z) {a g gi : G}
    (hneq_a : ∀ e ∈ centerIn (J z), g ≠ a * e)
    (hneq_gi : ∀ e ∈ centerIn (J z), a ≠ gi * e)
    (hgi_not_g_mul : ∀ e ∈ centerIn (J z), gi ≠ g * e) :
    SixDistinct z a g gi := by
  have hz_mem : z ∈ centerIn (J z) := z_mem_centerIn_J h
  have hone : (1 : G) ∈ centerIn (J z) := Subgroup.one_mem _
  have hz2 : z * z = 1 := z_mul_self h
  have h_a_g : a ≠ g := fun he => hneq_a 1 hone (by simpa using he.symm)
  have h_a_gi : a ≠ gi := fun he => hneq_gi 1 hone (by simpa using he)
  have h_g_gi : g ≠ gi := fun he => hgi_not_g_mul 1 hone (by simpa using he.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    have h1 : (1 : G) = z := by
      have := congrArg (fun y => a⁻¹ * y) he
      simpa [mul_assoc] using this
    exact z_ne_one h h1.symm
  · exact fun he => hneq_a 1 hone (by simpa using he.symm)
  · intro he
    apply hneq_a z hz_mem
    calc g = (g * z) * z := by rw [mul_assoc, hz2, mul_one]
      _ = a * z := by rw [← he]
  · exact fun he => hneq_gi 1 hone (by simpa using he)
  · exact fun he => hneq_gi z hz_mem he
  · exact fun he => hneq_a z hz_mem (by simpa using he.symm)
  · exact fun he => h_a_g (mul_right_cancel he)
  · intro he
    apply hneq_gi z hz_mem
    calc a = (a * z) * z := by rw [mul_assoc, hz2, mul_one]
      _ = gi * z := by rw [he]
  · exact fun he => h_a_gi (mul_right_cancel he)
  · intro he
    have h1 : (1 : G) = z := by
      have := congrArg (fun y => g⁻¹ * y) he
      simpa [mul_assoc] using this
    exact z_ne_one h h1.symm
  · exact fun he => hgi_not_g_mul 1 hone (by simpa using he.symm)
  · intro he
    apply hgi_not_g_mul z hz_mem
    calc gi = gi * z * z := by rw [mul_assoc, hz2, mul_one]
      _ = g * z := by rw [← he]
  · exact fun he => hgi_not_g_mul z hz_mem he.symm
  · exact fun he => h_g_gi (mul_right_cancel he)
  · intro he
    have h1 : (1 : G) = z := by
      have := congrArg (fun y => gi⁻¹ * y) he
      simpa [mul_assoc] using this
    exact z_ne_one h h1.symm

private theorem sigma54_cube (D : QuotientData (z := z) hN) :
    ((sigma1Nine (z := z) D : ↥(H z)) : G) *
    ((sigma1Nine (z := z) D : ↥(H z)) : G) * ((sigma1Nine (z := z) D : ↥(H z)) : G) = 1 := by
  have h := congrArg Subtype.val (pow_orderOf_eq_one (sigma1Nine (z := z) D))
  rw [sigma1Nine_order (z := z) D] at h
  simpa [pow_three'] using h

private theorem sigma54_inv2 (D : QuotientData (z := z) hN)
    (hσ1 : ((sigma1Nine (z := z) D : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D : ↥(H z)) : G) = 1) :
    ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ =
      ((sigma1Nine (z := z) D : ↥(H z)) : G) := by
  rw [← mul_inv_rev]
  exact inv_eq_of_mul_eq_one_right hσ1

private theorem sigma54_sqinv (D : QuotientData (z := z) hN)
    (hσ1 : ((sigma1Nine (z := z) D : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D : ↥(H z)) : G) = 1) :
    ((sigma1Nine (z := z) D : ↥(H z)) : G) *
      ((sigma1Nine (z := z) D : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ :=
  eq_inv_of_mul_eq_one_left hσ1

private theorem gi_ne_g_mul (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a e : G} (he : e ∈ centerIn (J z))
    (hneq_a : ∀ e ∈ centerIn (J z),
      ((sigma1Nine (z := z) D : ↥(H z)) : G) * a *
        ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ ≠ a * e) :
    ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ * a *
        ((sigma1Nine (z := z) D : ↥(H z)) : G) ≠
      ((sigma1Nine (z := z) D : ↥(H z)) : G) * a *
        ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ * e := by
  intro hge
  let s1 : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  have hσ1 := sigma54_cube D
  have hσ1inv2 := sigma54_inv2 D hσ1
  have hσ1sqinv := sigma54_sqinv D hσ1
  have he2 : e * e = 1 := centerIn_J_sq h he
  have hσ1e : Commute s1 e := sigma_commute_of_mem_centerIn_of (z := z) (conjZ_sigma1Nine h D) he
  have hgi_conj : s1⁻¹ * (s1⁻¹ * a * s1) * s1 = s1 * a * s1⁻¹ := by
    calc s1⁻¹ * (s1⁻¹ * a * s1) * s1 = (s1⁻¹ * s1⁻¹) * a * (s1 * s1) := by group
      _ = s1 * a * s1⁻¹ := by rw [hσ1inv2, hσ1sqinv]
  have hg_eq_gi : s1 * a * s1⁻¹ = s1⁻¹ * a * s1 * e := by
    calc s1 * a * s1⁻¹ = (s1 * a * s1⁻¹) * 1 := (mul_one _).symm
      _ = (s1 * a * s1⁻¹) * (e * e) := by rw [he2]
      _ = (s1 * a * s1⁻¹ * e) * e := by group
      _ = (s1⁻¹ * a * s1) * e := by rw [hge]
  have ha_eq : a = s1 * a * s1⁻¹ * e := by
    calc a = s1⁻¹ * (s1 * a * s1⁻¹) * s1 := by group
      _ = s1⁻¹ * ((s1⁻¹ * a * s1) * e) * s1 := by rw [hg_eq_gi]
      _ = (s1⁻¹ * (s1⁻¹ * a * s1) * s1) * e := by
          calc s1⁻¹ * ((s1⁻¹ * a * s1) * e) * s1 =
              s1⁻¹ * (s1⁻¹ * a * s1) * (e * s1) := by group
            _ = s1⁻¹ * (s1⁻¹ * a * s1) * (s1 * e) := by rw [hσ1e.symm]
            _ = (s1⁻¹ * (s1⁻¹ * a * s1) * s1) * e := by group
      _ = s1 * a * s1⁻¹ * e := by rw [hgi_conj]
  have hg_eq : s1 * a * s1⁻¹ = a * e := by
    calc s1 * a * s1⁻¹ = (s1 * a * s1⁻¹) * 1 := (mul_one _).symm
      _ = (s1 * a * s1⁻¹) * (e * e) := by rw [he2]
      _ = (s1 * a * s1⁻¹ * e) * e := by group
      _ = a * e := by rw [← ha_eq]
  exact hneq_a e he hg_eq

private theorem conj_to_a (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {X : Set G} {a b : G}
    (hmemN : ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G))
    (hXZ : ∀ a ∈ X, a ∉ centerIn (J z)) (ha : a ∈ X) (hb : b = a ∨ b = a * z) :
    ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      c * a * c⁻¹ = b := by
  rcases hb with rfl | rfl
  · exact ⟨1, (lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
      (τ : G)).one_mem, by group⟩
  · obtain ⟨q, hq, hqa⟩ := exists_conj_eq_mul_z_of_not_mem_centerIn (z := z) (D := D)
      h hσ₂ hq₂ hc₂ (n := a) (hmemN ha).1 (hXZ a ha)
    exact ⟨q, mem_lemma54N₀_of_mem_J (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq,
      hqa⟩

private theorem conj_to_g (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {X : Set G} {a g b : G}
    (hmemN : ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G))
    (hXZ : ∀ a ∈ X, a ∉ centerIn (J z)) (hgaX : g ∈ X)
    (hg : g = ((sigma1Nine (z := z) D : ↥(H z)) : G) * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹)
    (hb : b = g ∨ b = g * z) :
    ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      c * a * c⁻¹ = b := by
  let s1 : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  rcases hb with rfl | rfl
  · exact ⟨s1, sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁, hg.symm⟩
  · obtain ⟨q, hq, hqg⟩ := exists_conj_eq_mul_z_of_not_mem_centerIn (z := z) (D := D)
      h hσ₂ hq₂ hc₂ (n := g) (hmemN hgaX).1 (hXZ g hgaX)
    refine ⟨q * s1, (lemma54N₀ (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).mul_mem
      (mem_lemma54N₀_of_mem_J (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq)
      (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁), ?_⟩
    have heq : (q * s1) * a * (q * s1)⁻¹ = q * g * q⁻¹ := by
      rw [hg]
      dsimp [s1]
      group
    rw [heq, hqg]

private theorem conj_to_gi (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {X : Set G} {a gi b : G}
    (hmemN : ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G))
    (hXZ : ∀ a ∈ X, a ∉ centerIn (J z)) (hgiaX : gi ∈ X)
    (hgi : gi = ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G))
    (hb : b = gi ∨ b = gi * z) :
    ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      c * a * c⁻¹ = b := by
  let s1 : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  rcases hb with rfl | rfl
  · exact ⟨s1⁻¹, (lemma54N₀ (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).inv_mem
      (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁), by
        simpa [s1] using hgi.symm⟩
  · obtain ⟨q, hq, hqgi⟩ := exists_conj_eq_mul_z_of_not_mem_centerIn (z := z) (D := D)
      h hσ₂ hq₂ hc₂ (n := gi) (hmemN hgiaX).1 (hXZ gi hgiaX)
    refine ⟨q * s1⁻¹, (lemma54N₀ (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).mul_mem
      (mem_lemma54N₀_of_mem_J (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq)
      ((lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).inv_mem
        (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁)), ?_⟩
    have heq : (q * s1⁻¹) * a * (q * s1⁻¹)⁻¹ = q * gi * q⁻¹ := by
      rw [hgi]
      dsimp [s1]
      group
    rw [heq, hqgi]

private theorem exists_conj_to_sixFun (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {X : Set G} {a g gi : G}
    (hmemN : ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G))
    (hXZ : ∀ a ∈ X, a ∉ centerIn (J z)) (ha : a ∈ X) (hgaX : g ∈ X) (hgiaX : gi ∈ X)
    (hg : g = ((sigma1Nine (z := z) D : ↥(H z)) : G) * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹)
    (hgi : gi = ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G))
    {b : G} (hb : b ∈ Set.range (sixFun z a g gi)) :
    ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      c * a * c⁻¹ = b := by
  obtain ⟨i, rfl⟩ := hb
  fin_cases i
  · exact conj_to_a (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hmemN hXZ ha
      (Or.inl rfl)
  · exact conj_to_a (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hmemN hXZ ha
      (Or.inr rfl)
  · exact conj_to_g (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hmemN hXZ hgaX hg
      (Or.inl rfl)
  · exact conj_to_g (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hmemN hXZ hgaX hg
      (Or.inr rfl)
  · exact conj_to_gi (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hmemN hXZ hgiaX hgi
      (Or.inl rfl)
  · exact conj_to_gi (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hmemN hXZ hgiaX hgi
      (Or.inr rfl)

private theorem memN_of_mem_X (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    {X : Set G}
    (hXJ : X ⊆ J z)
    (hXW : X ⊆ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) :
    ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G) := by
  have hτG : (τ : G) * (τ : G) = 1 := tau_mul_self_val hτ
  have hτJ : (τ : G) ∉ J z := tau_not_mem_J (z := z) (D := D) hqτ
  intro n hn
  have hc := (mem_lemma54W_iff_of_mem_J (z := z)
    (σ := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (τ := (τ : G)) hτG hτJ
    (hXJ hn)).mp (hXW hn)
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hXJ hn, hc.1⟩, hc.2⟩

private theorem sigma1_conj_ne_mul_of_memN (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G}
    (hn : a ∈ J z ⊓ centralizer ({sigma54 D σ₂} : Set G) ⊓ centralizer ({(τ : G)} : Set G))
    (haZ : a ∉ centerIn (J z)) :
    ∀ e ∈ centerIn (J z), ((sigma1Nine (z := z) D : ↥(H z)) : G) * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ ≠ a * e := by
  intro e he
  exact sigma1Nine_conj_ne_mul_of_not_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂ hc₂
    hqτ hτ₁ hτ₂ hn haZ he

private theorem sixDistinct_of_mem_X (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {X : Set G} {a g gi : G}
    (hmemN : ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G))
    (hXZ : ∀ a ∈ X, a ∉ centerIn (J z)) (hXN : ∀ c ∈ lemma54N₀ (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G), ∀ a ∈ X, c * a * c⁻¹ ∈ X)
    (ha : a ∈ X)
    (hg : g = ((sigma1Nine (z := z) D : ↥(H z)) : G) * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹)
    (hgi : gi = ((sigma1Nine (z := z) D : ↥(H z)) : G)⁻¹ * a *
      ((sigma1Nine (z := z) D : ↥(H z)) : G)) :
    SixDistinct z a g gi := by
  let s1 : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  have hgaX : g ∈ X := by
    simpa [hg] using hXN s1 (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁) a ha
  have hgiaX : gi ∈ X := by
    simpa [hgi] using hXN s1⁻¹
      ((lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).inv_mem
        (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁)) a ha
  have hneq_a : ∀ e ∈ centerIn (J z), s1 * a * s1⁻¹ ≠ a * e := by
    simpa [s1] using sigma1_conj_ne_mul_of_memN (z := z) (D := D) h P hP hσ₂ hq₂ hc₂
      hqτ hτ₁ hτ₂ (hmemN ha) (hXZ a ha)
  have hgiaX' : s1⁻¹ * a * s1 ∈ X := by simpa [hgi] using hgiaX
  have hneq_gi : ∀ e ∈ centerIn (J z), a ≠ s1⁻¹ * a * s1 * e := by
    intro e he
    have h := sigma1Nine_conj_ne_mul_of_not_mem_centerIn (z := z) (D := D) h P hP hσ₂ hq₂
      hc₂ hqτ hτ₁ hτ₂ (n := s1⁻¹ * a * s1) (hmemN hgiaX') (hXZ (s1⁻¹ * a * s1) hgiaX') he
    have hconj : s1 * (s1⁻¹ * a * s1) * s1⁻¹ = a := by group
    rwa [hconj] at h
  have hneq_a_g : ∀ e ∈ centerIn (J z), g ≠ a * e := by
    intro e he
    rw [hg]
    exact hneq_a e he
  have hneq_gi_gi : ∀ e ∈ centerIn (J z), a ≠ gi * e := by
    intro e he
    rw [hgi]
    exact hneq_gi e he
  have hgi_not_g_mul : ∀ e ∈ centerIn (J z), gi ≠ g * e := by
    intro e he
    simpa [hg, hgi] using gi_ne_g_mul (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ
      hτ₁ hτ₂ he (by simpa [hg, s1] using hneq_a_g)
  exact six_ineq (z := z) (a := a) (g := g) (gi := gi) h hneq_a_g hneq_gi_gi hgi_not_g_mul

private theorem transitive_of_six (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {X : Set G}
    (hXJ : X ⊆ J z)
    (hXW : X ⊆ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
    (hXZ : ∀ a ∈ X, a ∉ centerIn (J z)) (hXcard : X.ncard = 6)
    (hXz : ∀ a ∈ X, a * z ∈ X)
    (hXN : ∀ c ∈ lemma54N₀ (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G), ∀ a ∈ X, c * a * c⁻¹ ∈ X) :
    ∀ a ∈ X, ∀ b ∈ X,
      ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
        c * a * c⁻¹ = b := by
  have hmemN : ∀ {n : G}, n ∈ X →
      n ∈ J z ⊓ centralizer
        ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(τ : G)} : Set G) :=
    memN_of_mem_X (z := z) (D := D) (σ₂ := σ₂) (τ := τ) h hqτ hτ hXJ hXW
  intro a ha
  let s1 : G := ((sigma1Nine (z := z) D : ↥(H z)) : G)
  let g : G := s1 * a * s1⁻¹
  let gi : G := s1⁻¹ * a * s1
  have hgaX : g ∈ X := by
    simpa [g] using hXN s1 (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁) a ha
  have hgiaX : gi ∈ X := by
    simpa [gi] using hXN s1⁻¹
      ((lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)).inv_mem
        (sigma1Nine_mem_lemma54N₀ (z := z) (D := D) h hc₂ hτ₁)) a ha
  have hdist : SixDistinct z a g gi :=
    sixDistinct_of_mem_X (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hmemN hXZ hXN ha rfl rfl
  have hXeq : X = Set.range (sixFun z a g gi) :=
    six_eq_range hdist ha (hXz a ha) hgaX (hXz g hgaX) hgiaX (hXz gi hgiaX) hXcard
  intro b hb
  have hb' : b ∈ Set.range (sixFun z a g gi) := by rwa [← hXeq]
  exact exists_conj_to_sixFun (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    hmemN hXZ ha hgaX hgiaX rfl rfl hb'

theorem exists_conj_eq_of_mem_lemma54O2 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (∀ a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
      ∀ b ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
        ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
          c * a * c⁻¹ = b) ∧
      ∀ a ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁,
        ∀ b ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁,
          ∃ c ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
            c * a * c⁻¹ = b := by
  constructor
  · exact transitive_of_six (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (X := lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
      (fun a ha => mem_J_of_mem_O2 (z := z) ha)
      (fun a ha => (mem_lemma54W_of_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP
        hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha).1)
      (fun a ha => (mem_lemma54W_of_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP
        hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha).2.2)
      (ncard_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
      (fun a ha => (mul_z_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
        hqτ hτ hτ₁ hτ₂).1 a ha)
      (fun c hc a ha => (conj_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂
        hc₂ hqτ hτ hτ₁ hτ₂ hc).1 a ha)
  · exact transitive_of_six (z := z) (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (X := lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁)
      (fun a ha => mem_J_of_mem_O3 (z := z) ha)
      (fun a ha => (mem_lemma54W_of_mem_lemma54O3 (z := z) (D := D) h hz₁ hz₁z hord P hP
        hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha).1)
      (fun a ha => (mem_lemma54W_of_mem_lemma54O3 (z := z) (D := D) h hz₁ hz₁z hord P hP
        hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha).2.2)
      (ncard_lemma54O3 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂)
      (fun a ha => (mul_z_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
        hqτ hτ hτ₁ hτ₂).2 a ha)
      (fun c hc a ha => (conj_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂
        hc₂ hqτ hτ hτ₁ hτ₂ hc).2 a ha)

private theorem mul_z1_mem_O3 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G}
    (ha : a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) :
    a * z₁ ∈ lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁ := by
  simp only [lemma54O2, Set.mem_setOf_eq] at ha
  obtain ⟨haJ, hlab, ha1, haz⟩ := ha
  have hz1τ : z₁ * (τ : G) = (τ : G) * z₁ :=
    z1_comm_tau (z := z) (D := D) h hz₁ P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
  have hz1sq : z₁ * z₁ = 1 := centerIn_J_sq h hz₁
  have hz1z : z₁ * z = z * z₁ := z1_comm_z h hz₁
  have hlabel_z1 : ∀ {x e : G},
      IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e →
      IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
        (x * z₁) (e * z₁) := by
    intro x e hx
    obtain ⟨q, hq, hx⟩ := hx
    refine ⟨q, hq, ?_⟩
    calc x * z₁ = (q * (τ : G) * q⁻¹ * e) * z₁ := by rw [hx]
      _ = q * (τ : G) * q⁻¹ * (e * z₁) := by group
  refine ⟨(J z).mul_mem haJ hz₁.1, ?_, ?_, ?_⟩
  · rcases hlab with hlab | hlab
    · left
      have h := hlabel_z1 hlab
      rw [show (a * (τ : G)) * z₁ = (a * z₁) * (τ : G) by rw [mul_assoc, ← hz1τ, ← mul_assoc]] at h
      simpa using h
    · right
      have h := hlabel_z1 hlab
      rw [show (a * (τ : G)) * z₁ = (a * z₁) * (τ : G) by rw [mul_assoc, ← hz1τ, ← mul_assoc]] at h
      simpa [hz1z] using h
  · intro he
    apply ha1
    calc a = (a * z₁) * z₁ := by rw [mul_assoc, hz1sq, mul_one]
      _ = z₁ * z₁ := by rw [he]
      _ = 1 := hz1sq
  · intro he
    apply haz
    calc a = (a * z₁) * z₁ := by rw [mul_assoc, hz1sq, mul_one]
      _ = (z₁ * z) * z₁ := by rw [he]
      _ = z := by rw [mul_assoc, ← hz1z, ← mul_assoc, hz1sq, one_mul]

private theorem centerIn_mem_closure (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) {a : G}
    (ha : a ∈ lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)) :
    z ∈ Subgroup.closure
        (lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∪
          lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁) ∧
      z₁ ∈ Subgroup.closure
        (lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∪
          lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁) ∧
      z₁ * z ∈ Subgroup.closure
        (lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∪
          lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁) := by
  have haz : a * z ∈ lemma54O2 (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) :=
    (mul_z_mem_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ
      hτ₁ hτ₂).1 a ha
  have haz1 : a * z₁ ∈ lemma54O3 (z := z)
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁ :=
    mul_z1_mem_O3 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha
  let S : Set G := lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∪
    lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁
  have haS : a ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inl ha)
  have hzS : z ∈ Subgroup.closure S := by
    have h := (Subgroup.closure S).mul_mem ((Subgroup.closure S).inv_mem haS)
      (Subgroup.subset_closure (Or.inl haz))
    simpa [mul_assoc] using h
  have hz1S : z₁ ∈ Subgroup.closure S := by
    have h := (Subgroup.closure S).mul_mem ((Subgroup.closure S).inv_mem haS)
      (Subgroup.subset_closure (Or.inr haz1))
    simpa [mul_assoc] using h
  exact ⟨by simpa [S] using hzS, by simpa [S] using hz1S,
    by simpa [S] using (Subgroup.closure S).mul_mem hz1S hzS⟩

theorem J_inf_lemma54W_le_closure (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    J z ⊓ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ≤
      Subgroup.closure
        (lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∪
          lemma54O3 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁) := by
  have hO2ne : lemma54O2 (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ≠ ∅ := by
    intro hempty
    have hcard := ncard_lemma54O2 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hO2ne
  obtain ⟨hzS, hz1S, hz1zS⟩ := centerIn_mem_closure (z := z) (D := D) h hz₁ hz₁z hord
    P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha
  intro n hn
  obtain ⟨hnJ, hnW⟩ := Subgroup.mem_inf.mp hn
  rcases mem_lemma54O2_or_mem_lemma54O3 (z := z) (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
    hqτ hτ hτ₁ hτ₂ hnW hnJ with h1 | h1 | h1 | h1 | h1 | h1
  · subst n; exact Subgroup.one_mem _
  · subst n; exact hzS
  · subst n; exact hz1S
  · subst n; exact hz1zS
  · exact Subgroup.subset_closure (Or.inl h1)
  · exact Subgroup.subset_closure (Or.inr h1)

end CFSG.RankThree.GF2n.Parrott
