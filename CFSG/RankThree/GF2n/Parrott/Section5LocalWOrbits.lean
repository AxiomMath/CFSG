module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalWOrbitsJ
public import CFSG.RankThree.GF2n.Parrott.Section5LocalWOrbitsOut
public import CFSG.RankThree.GF2n.Parrott.Section5NoFusionO4
import all CFSG.RankThree.GF2n.Parrott.Section5Lemma54Orbits

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

private lemma conj_eq_self_of_mem_centerIn_of_mem_centralizer_z1
    (h : Tim79a.ParrottHyp z) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {g e : G} (hgH : g ∈ H z) (hgz₁ : g ∈ centralizer ({z₁} : Set G))
    (he : e ∈ centerIn (J z)) :
    g * e * g⁻¹ = e := by
  have hgz : g * z * g⁻¹ = z := by
    have hcomm : g * z = z * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H_eq_centralizer] using hgH)
    rw [hcomm, mul_inv_cancel_right]
  have hgz₁' : g * z₁ * g⁻¹ = z₁ := by
    have hcomm : g * z₁ = z₁ * g := Subgroup.mem_centralizer_singleton_iff.mp hgz₁
    rw [hcomm, mul_inv_cancel_right]
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with rfl | rfl | rfl | rfl
  · simp
  · exact hgz
  · exact hgz₁'
  · calc g * (z * z₁) * g⁻¹ = (g * z * g⁻¹) * (g * z₁ * g⁻¹) := by group
      _ = z * z₁ := by rw [hgz, hgz₁']

private lemma exists_conj_eq_of_mem_outer {σ τ : G} {N : Subgroup G} {e : G}
    (he : e ∈ centerIn (J z))
    (hQN : ∀ q ∈ J z ⊓ centralizer ({σ} : Set G), q ∈ N)
    {a b : G} (ha : IsLemma54Label (z := z) σ τ a e)
    (hb : IsLemma54Label (z := z) σ τ b e) :
    ∃ c ∈ N, c * a * c⁻¹ = b := by
  obtain ⟨q₁, hq₁, rfl⟩ := ha
  obtain ⟨q₂, hq₂, rfl⟩ := hb
  have hcQ : q₂ * q₁⁻¹ ∈ J z ⊓ centralizer ({σ} : Set G) :=
    Subgroup.mem_inf.mpr ⟨(J z).mul_mem hq₂.1 ((J z).inv_mem hq₁.1),
      (Subgroup.centralizer ({σ} : Set G)).mul_mem hq₂.2
        ((Subgroup.centralizer ({σ} : Set G)).inv_mem hq₁.2)⟩
  refine ⟨q₂ * q₁⁻¹, hQN _ hcQ, ?_⟩
  have he₁ : q₁⁻¹ * e = e * q₁⁻¹ :=
    Subgroup.mem_centralizer_iff.mp he.2 q₁⁻¹ ((J z).inv_mem hq₁.1)
  have he₂ : q₂⁻¹ * e = e * q₂⁻¹ :=
    Subgroup.mem_centralizer_iff.mp he.2 q₂⁻¹ ((J z).inv_mem hq₂.1)
  calc (q₂ * q₁⁻¹) * (q₁ * τ * q₁⁻¹ * e) * (q₂ * q₁⁻¹)⁻¹
      = q₂ * τ * (q₁⁻¹ * e * q₁) * q₂⁻¹ := by group
    _ = q₂ * τ * e * q₂⁻¹ := by rw [he₁]; group
    _ = q₂ * τ * q₂⁻¹ * e := by
        calc q₂ * τ * e * q₂⁻¹ = q₂ * τ * (e * q₂⁻¹) := by group
          _ = q₂ * τ * (q₂⁻¹ * e) := by rw [← he₂]
          _ = q₂ * τ * q₂⁻¹ * e := by group

private lemma isLemma54Label_conj_of_not_mem_centralizer {σ τ g e e' ℓ₀ z₁ : G}
    {N : Subgroup G}
    (hlabel : ∀ g ∈ N, g ∉ centralizer ({z₁} : Set G) → ∀ x e,
      IsLemma54Label (z := z) σ τ x e →
      IsLemma54Label (z := z) σ τ (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹)))
    (hgN : g ∈ N) (hgz₁ : g ∉ centralizer ({z₁} : Set G))
    (heq : ℓ₀ * (g * e * g⁻¹) = e') :
    ∀ x, IsLemma54Label (z := z) σ τ x e →
      IsLemma54Label (z := z) σ τ (g * x * g⁻¹) e' := by
  intro x hx
  have h := hlabel g hgN hgz₁ x e hx
  rwa [heq] at h

private lemma isLemma54Label_conj_of_mem_centralizer {σ τ g x e : G}
    (hgH : g ∈ H z) (hgσ : g ∈ centralizer ({σ} : Set G))
    (hgτ : IsLemma54Label (z := z) σ τ (g * τ * g⁻¹) 1)
    (he : e ∈ centerIn (J z)) (hefix : g * e * g⁻¹ = e)
    (hx : IsLemma54Label (z := z) σ τ x e) :
    IsLemma54Label (z := z) σ τ (g * x * g⁻¹) e := by
  have h := isLemma54Label_conj hgH hgσ (Subgroup.one_mem _) hgτ hx
  simpa [hefix] using h

private lemma outer_label_equations {g ℓ₀ lam z₁ : G}
    (hkey : ℓ₀ * (g * lam * g⁻¹) = lam * z)
    (hgz : g * z * g⁻¹ = z) (hgz₁ : g * z₁ * g⁻¹ = z₁ * z)
    (hz2 : z * z = 1) (hzz₁ : z * z₁ = z₁ * z) :
    (ℓ₀ * (g * (lam * z) * g⁻¹) = lam) ∧
      (ℓ₀ * (g * (lam * z₁) * g⁻¹) = lam * z₁) ∧
      (ℓ₀ * (g * (lam * z₁ * z) * g⁻¹) = lam * z₁ * z) := by
  have h1 : g * (lam * z) * g⁻¹ = (g * lam * g⁻¹) * z := by
    calc g * (lam * z) * g⁻¹ = (g * lam * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * lam * g⁻¹) * z := by rw [hgz]
  have h2 : g * (lam * z₁) * g⁻¹ = (g * lam * g⁻¹) * (z₁ * z) := by
    calc g * (lam * z₁) * g⁻¹ = (g * lam * g⁻¹) * (g * z₁ * g⁻¹) := by group
      _ = (g * lam * g⁻¹) * (z₁ * z) := by rw [hgz₁]
  have h3 : g * (lam * z₁ * z) * g⁻¹ = (g * lam * g⁻¹) * (z₁ * z) * z := by
    calc g * (lam * z₁ * z) * g⁻¹
        = (g * lam * g⁻¹) * (g * z₁ * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * lam * g⁻¹) * (z₁ * z) * z := by rw [hgz₁, hgz]
  have h2eq : (lam * z) * (z₁ * z) = lam * z₁ := by
    calc (lam * z) * (z₁ * z) = lam * (z * z₁) * z := by group
      _ = lam * (z₁ * z) * z := by rw [hzz₁]
      _ = lam * z₁ * (z * z) := by group
      _ = lam * z₁ := by rw [hz2, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, ← mul_assoc, hkey]
    rw [mul_assoc, hz2, mul_one]
  · rw [h2, ← mul_assoc, hkey]
    exact h2eq
  · rw [h3]
    calc ℓ₀ * ((g * lam * g⁻¹) * (z₁ * z) * z)
        = (ℓ₀ * ((g * lam * g⁻¹) * (z₁ * z))) * z := by group
      _ = ((ℓ₀ * (g * lam * g⁻¹)) * (z₁ * z)) * z := by group
      _ = ((lam * z) * (z₁ * z)) * z := by rw [hkey]
      _ = (lam * z₁) * z := by rw [h2eq]

private lemma conj_eq_self_of_mem_centerIn {e q : G}
    (he : e ∈ centerIn (J z)) (hq : q ∈ J z) :
    q * e * q⁻¹ = e := by
  have hcomm : q * e = e * q := Subgroup.mem_centralizer_iff.mp he.2 q hq
  rw [hcomm]
  group

private lemma conj_mul_eq_of_conj_eq {g a b : G}
    (ha : g * a * g⁻¹ = a) (hb : g * b * g⁻¹ = b) :
    g * (a * b) * g⁻¹ = a * b := by
  rw [← conj_mul, ha, hb]

private lemma disjoint_outer {σ τ e e' : G}
    (hunique : ∀ {x : G}, e ∈ centerIn (J z) → e' ∈ centerIn (J z) →
      IsLemma54Label (z := z) σ τ x e → IsLemma54Label (z := z) σ τ x e' → e = e')
    (he : e ∈ centerIn (J z)) (he' : e' ∈ centerIn (J z)) (hne : e ≠ e') :
    Disjoint ({x : G | IsLemma54Label (z := z) σ τ x e})
      ({x : G | IsLemma54Label (z := z) σ τ x e'}) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hne (hunique he he' hx hx')

private noncomputable def lemma54Outer (z σ τ e : G) : Set G :=
  {x : G | IsLemma54Label (z := z) σ τ x e}

private noncomputable def lemma54OuterF (z σ τ e : G) : Finset G :=
  (lemma54Outer z σ τ e).toFinite.toFinset

private noncomputable def lemma54O2F (z σ τ : G) : Finset G :=
  (lemma54O2 (z := z) σ τ).toFinite.toFinset

private noncomputable def lemma54O3F (z σ τ z₁ : G) : Finset G :=
  (lemma54O3 (z := z) σ τ z₁).toFinite.toFinset

private noncomputable def lemma54OrbitFamily [DecidableEq G]
    (z σ τ z₁ lam : G) : Fin 7 → Finset G :=
  ![{z}, {z₁, z₁ * z}, lemma54O2F z σ τ, lemma54O3F z σ τ z₁,
    lemma54OuterF z σ τ lam ∪ lemma54OuterF z σ τ (lam * z),
    lemma54OuterF z σ τ (lam * z₁), lemma54OuterF z σ τ (lam * z₁ * z)]

private lemma mem_lemma54OuterF {z σ τ e a : G} :
    a ∈ lemma54OuterF z σ τ e ↔ IsLemma54Label (z := z) σ τ a e := by
  simp [lemma54OuterF, lemma54Outer]

private lemma mem_lemma54O2F {z σ τ a : G} :
    a ∈ lemma54O2F z σ τ ↔ a ∈ lemma54O2 (z := z) σ τ := by
  simp [lemma54O2F]

private lemma mem_lemma54O3F {z σ τ z₁ a : G} :
    a ∈ lemma54O3F z σ τ z₁ ↔ a ∈ lemma54O3 (z := z) σ τ z₁ := by
  simp [lemma54O3F]

private lemma lemma54_z_sq (h : Tim79a.ParrottHyp z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [h.1, pow_two] at this

private lemma lemma54_z₁_sq {z₁ : G} (hord : orderOf z₁ = 2) : z₁ * z₁ = 1 := by
  have := pow_orderOf_eq_one z₁
  rwa [hord, pow_two] at this

private lemma lemma54_z_comm_z₁ (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) : z * z₁ = z₁ * z :=
  (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) z₁ (J_le_H hz₁.1)).symm

private lemma lemma54_z_ne_one (h : Tim79a.ParrottHyp z) : z ≠ 1 := by
  intro hz
  have := h.1
  rw [hz, orderOf_one] at this
  norm_num at this

private lemma lemma54_z₁_ne_one {z₁ : G} (hord : orderOf z₁ = 2) : z₁ ≠ 1 := by
  intro hz
  rw [hz, orderOf_one] at hord
  norm_num at hord

private lemma lemma54_z₁z_ne_one (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) :
    z₁ * z ≠ 1 := by
  intro hz
  have hz₁eq : z₁ = z := by
    calc z₁ = (z₁ * z) * z := by rw [mul_assoc, lemma54_z_sq h, mul_one]
      _ = 1 * z := by rw [hz]
      _ = z := one_mul z
  exact hz₁z (hz₁eq ▸ Subgroup.mem_zpowers z)

private lemma lemma54_tA_ne_one : (⟨t, t_mem_A⟩ : A45) ≠ 1 := by
  intro hq
  exact t_ne_one (congrArg Subtype.val hq)

private lemma lemma54_tau_not_mem_J (h : Tim79a.ParrottHyp z) {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) : (τ : G) ∉ J z := by
  intro hτJ
  have hq : qH (z := z) D τ = 1 :=
    (J_mem_iff D τ).mp (Subgroup.mem_subgroupOf.mpr hτJ)
  rw [hqτ] at hq
  exact lemma54_tA_ne_one hq

private lemma lemma54_outer_label_data [DecidableEq G]
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (σ τG : G)
    (hσ : σ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (hτG : τG = (τ : G)) :
    ∃ ℓ₀ lam : G,
      (ℓ₀ = 1 ∨ ℓ₀ = z) ∧ (lam = 1 ∨ lam = z₁) ∧
      (∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) → ∀ x e,
        IsLemma54Label (z := z) σ τG x e →
          IsLemma54Label (z := z) σ τG (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹))) ∧
      (∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
        ℓ₀ * (g * lam * g⁻¹) = lam * z) := by
  obtain ⟨ℓ₀, hℓ₀, hlabel⟩ :=
    exists_lemma54_outer_label (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  have hlabel' : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
      ∀ x e, IsLemma54Label (z := z) σ τG x e →
        IsLemma54Label (z := z) σ τG (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹)) := by
    simpa only [hσ, hτG] using hlabel
  let lam : G := if ℓ₀ = z then 1 else z₁
  have hlam : lam = 1 ∨ lam = z₁ := by
    by_cases hℓz : ℓ₀ = z
    · left; simp only [lam, if_pos hℓz]
    · right; simp only [lam, if_neg hℓz]
  have hkey : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
      ℓ₀ * (g * lam * g⁻¹) = lam * z := by
    intro g hgN hgz₁
    rcases hlam with hlam1 | hlamz₁
    · have hℓz : ℓ₀ = z := by
        by_contra hℓz
        have hlam_eq : lam = z₁ := by simp only [lam, if_neg hℓz]
        rw [hlam_eq] at hlam1
        exact lemma54_z₁_ne_one hord hlam1
      rw [hlam1, hℓz]; simp
    · have hℓ1 : ℓ₀ = 1 := by
        by_contra hℓ1
        have hℓz : ℓ₀ = z := hℓ₀.resolve_left hℓ1
        have hlam_eq : lam = 1 := by simp only [lam, if_pos hℓz]
        rw [hlam_eq] at hlamz₁
        exact lemma54_z₁_ne_one hord hlamz₁.symm
      have hgH : g ∈ H z := (Subgroup.mem_inf.mp hgN).2
      have hconj := conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hgH hgz₁
      rw [hlamz₁, hℓ1, hconj, lemma54_z_comm_z₁ h hz₁]; simp
  exact ⟨ℓ₀, lam, hℓ₀, hlam, hlabel', hkey⟩

private lemma lemma54_mu_data
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (σ τG : G)
    (hσ : σ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (hτG : τG = (τ : G)) :
    ∃ μ : G, μ ∈ lemma54N₀ (z := z) σ τG ∧ μ ∉ centralizer ({z₁} : Set G) ∧
      μ ∈ H z ∧ μ * z * μ⁻¹ = z ∧ μ * z₁ * μ⁻¹ = z₁ * z := by
  obtain ⟨μ, hμN, hμz₁⟩ :=
    exists_mem_lemma54N₀_not_mem_centralizer_z1 (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
      hqτ hτ hτ₁ hτ₂
  have hμN' : μ ∈ lemma54N₀ (z := z) σ τG := by simpa only [hσ, hτG] using hμN
  have hμH : μ ∈ H z := (Subgroup.mem_inf.mp hμN').2
  have hμz : μ * z * μ⁻¹ = z := by
    have hcomm : μ * z = z * μ :=
      Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H_eq_centralizer] using hμH)
    rw [hcomm, mul_inv_cancel_right]
  have hμz₁' : μ * z₁ * μ⁻¹ = z₁ * z := by
    rw [conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hμH hμz₁,
      lemma54_z_comm_z₁ h hz₁]
  exact ⟨μ, hμN', hμz₁, hμH, hμz, hμz₁'⟩

private structure Lemma54Basic (z z₁ σ τG ℓ₀ lam μ : G) : Prop where
  hℓ₀ : ℓ₀ = 1 ∨ ℓ₀ = z
  hlam : lam = 1 ∨ lam = z₁
  hlabel : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
    ∀ x e, IsLemma54Label (z := z) σ τG x e →
      IsLemma54Label (z := z) σ τG (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹))
  hkey : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
    ℓ₀ * (g * lam * g⁻¹) = lam * z
  hz2 : z * z = 1
  hz₁sq : z₁ * z₁ = 1
  hzz₁ : z * z₁ = z₁ * z
  hz_ne_one : z ≠ 1
  hz₁_ne_one : z₁ ≠ 1
  hz₁z_ne_one : z₁ * z ≠ 1
  hτJ : τG ∉ J z
  hμN : μ ∈ lemma54N₀ (z := z) σ τG
  hμz₁ : μ ∉ centralizer ({z₁} : Set G)
  hμH : μ ∈ H z
  hμz : μ * z * μ⁻¹ = z
  hμz₁' : μ * z₁ * μ⁻¹ = z₁ * z

private structure Lemma54BlackA (z z₁ σ τG : G) : Prop where
  hz₁ : z₁ ∈ centerIn (J z)
  hz₁z : z₁ ∉ Subgroup.zpowers z
  hzC : z ∈ centerIn (J z)
  hmem_centerIn_J : ∀ {e : G}, e ∈ centerIn (J z) → e = 1 ∨ e = z ∨ e = z₁ ∨ e = z * z₁
  hQN : ∀ q ∈ J z ⊓ centralizer ({σ} : Set G), q ∈ lemma54N₀ (z := z) σ τG
  hunique : ∀ {x e e' : G}, e ∈ centerIn (J z) → e' ∈ centerIn (J z) →
    IsLemma54Label (z := z) σ τG x e → IsLemma54Label (z := z) σ τG x e' → e = e'
  hmemW : ∀ {x e : G}, e ∈ centerIn (J z) →
    IsLemma54Label (z := z) σ τG x e → x ∈ lemma54W z σ τG ∧ x ∉ J z
  hzW : z ∈ lemma54W z σ τG
  hzJ : z ∈ J z
  hz₁J : z₁ ∈ J z
  hcenter_le : centerIn (J z) ≤ J z ⊓ centralizer ({σ} : Set G) ⊓
    centralizer ({τG} : Set G)
  hO2mem : ∀ a ∈ lemma54O2 (z := z) σ τG,
    a ∈ lemma54W z σ τG ∧ a ∈ J z ∧ a ∉ centerIn (J z)
  hO3mem : ∀ a ∈ lemma54O3 (z := z) σ τG z₁,
    a ∈ lemma54W z σ τG ∧ a ∈ J z ∧ a ∉ centerIn (J z)
  hOuterCard : ∀ e ∈ centerIn (J z), (lemma54OuterF z σ τG e).card = 4
  hℓ1 : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∈ centralizer ({z₁} : Set G) →
    IsLemma54Label (z := z) σ τG (g * τG * g⁻¹) 1
  hconjz₁ : ∀ g ∈ H z, g ∉ centralizer ({z₁} : Set G) → g * z₁ * g⁻¹ = z₁ * z
  heq_self_centerIn : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∈ centralizer ({z₁} : Set G) →
    ∀ e ∈ centerIn (J z), g * e * g⁻¹ = e

private structure Lemma54BlackB (z z₁ σ τG : G) : Prop where
  hO2O3disj : Disjoint (lemma54O2 (z := z) σ τG) (lemma54O3 (z := z) σ τG z₁)
  hO2ncard : (lemma54O2 (z := z) σ τG).ncard = 6
  hO3ncard : (lemma54O3 (z := z) σ τG z₁).ncard = 6
  hO2trans : (∀ a ∈ lemma54O2 (z := z) σ τG, ∀ b ∈ lemma54O2 (z := z) σ τG,
      ∃ c ∈ lemma54N₀ (z := z) σ τG, c * a * c⁻¹ = b) ∧
    ∀ a ∈ lemma54O3 (z := z) σ τG z₁, ∀ b ∈ lemma54O3 (z := z) σ τG z₁,
      ∃ c ∈ lemma54N₀ (z := z) σ τG, c * a * c⁻¹ = b
  hO2inv : ∀ c ∈ lemma54N₀ (z := z) σ τG,
    (∀ a ∈ lemma54O2 (z := z) σ τG, c * a * c⁻¹ ∈ lemma54O2 (z := z) σ τG) ∧
      ∀ a ∈ lemma54O3 (z := z) σ τG z₁, c * a * c⁻¹ ∈ lemma54O3 (z := z) σ τG z₁
  hO2mulz : (∀ a ∈ lemma54O2 (z := z) σ τG, a * z ∈ lemma54O2 (z := z) σ τG) ∧
    ∀ a ∈ lemma54O3 (z := z) σ τG z₁, a * z ∈ lemma54O3 (z := z) σ τG z₁
  hgen0 : J z ⊓ lemma54W z σ τG ≤ Subgroup.closure
    (lemma54O2 (z := z) σ τG ∪ lemma54O3 (z := z) σ τG z₁)
  hO2orO3 : ∀ a ∈ lemma54W z σ τG, a ∈ J z →
    a = 1 ∨ a = z ∨ a = z₁ ∨ a = z₁ * z ∨
      a ∈ lemma54O2 (z := z) σ τG ∨ a ∈ lemma54O3 (z := z) σ τG z₁
  hexistsLabel : ∀ x ∈ lemma54W z σ τG, x ∉ J z →
    ∃ e ∈ centerIn (J z), IsLemma54Label (z := z) σ τG x e

private structure Lemma54Context (z z₁ σ τG ℓ₀ lam μ : G) : Prop where
  basic : Lemma54Basic z z₁ σ τG ℓ₀ lam μ
  blackA : Lemma54BlackA z z₁ σ τG
  blackB : Lemma54BlackB z z₁ σ τG

private lemma lemma54_basic [DecidableEq G] (h : Tim79a.ParrottHyp z)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (σ τG ℓ₀ lam μ : G) (hτG : τG = (τ : G))
    (hℓ₀ : ℓ₀ = 1 ∨ ℓ₀ = z) (hlam : lam = 1 ∨ lam = z₁)
    (hlabel : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
      ∀ x e, IsLemma54Label (z := z) σ τG x e →
        IsLemma54Label (z := z) σ τG (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹)))
    (hkey : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
      ℓ₀ * (g * lam * g⁻¹) = lam * z)
    (hμN : μ ∈ lemma54N₀ (z := z) σ τG) (hμz₁ : μ ∉ centralizer ({z₁} : Set G))
    (hμH : μ ∈ H z) (hμz : μ * z * μ⁻¹ = z) (hμz₁' : μ * z₁ * μ⁻¹ = z₁ * z) :
    Lemma54Basic z z₁ σ τG ℓ₀ lam μ :=
  { hℓ₀ := hℓ₀
    hlam := hlam
    hlabel := hlabel
    hkey := hkey
    hz2 := lemma54_z_sq h
    hz₁sq := lemma54_z₁_sq hord
    hzz₁ := lemma54_z_comm_z₁ h hz₁
    hz_ne_one := lemma54_z_ne_one h
    hz₁_ne_one := lemma54_z₁_ne_one hord
    hz₁z_ne_one := lemma54_z₁z_ne_one h hz₁ hz₁z
    hτJ := by simpa only [hτG] using lemma54_tau_not_mem_J (D := D) h hqτ
    hμN := hμN
    hμz₁ := hμz₁
    hμH := hμH
    hμz := hμz
    hμz₁' := hμz₁' }

private lemma lemma54_blackA (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (σ τG : G)
    (hσ : σ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (hτG : τG = (τ : G)) :
    Lemma54BlackA z z₁ σ τG := by
  cases hσ
  cases hτG
  exact
    { hz₁ := hz₁
      hz₁z := hz₁z
      hzC := z_mem_centerIn_J h
      hmem_centerIn_J := fun he => (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he
      hQN := fun q hq => mem_lemma54N₀_of_mem_J (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq
      hunique := fun he he' hx hx' =>
        isLemma54Label_unique (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he he' hx hx'
      hmemW := fun he hx =>
        mem_lemma54W_of_isLemma54Label (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he hx
      hzW := z_mem_lemma54W h
      hzJ := z_mem_J h
      hz₁J := hz₁.1
      hcenter_le := by
        simpa using
          centerIn_J_le_lemma54N (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂
      hO2mem := fun a ha =>
        mem_lemma54W_of_mem_lemma54O2 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha
      hO3mem := fun a ha =>
        mem_lemma54W_of_mem_lemma54O3 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ ha
      hOuterCard := by
        intro e he
        rw [lemma54OuterF, ← Set.ncard_eq_toFinset_card
          (lemma54Outer z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) e)
          (Set.toFinite _)]
        exact ncard_setOf_isLemma54Label (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ he
      hℓ1 := fun g hgN hgz₁ =>
        isLemma54Label_conj_tau_of_mem_centralizer_z1 (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
          hqτ hτ hτ₁ hτ₂ hgN hgz₁
      hconjz₁ := fun g hgH hgz₁ => by
        rw [conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hgH hgz₁,
          lemma54_z_comm_z₁ h hz₁]
      heq_self_centerIn := fun g hgN hgz₁ e he =>
        conj_eq_self_of_mem_centerIn_of_mem_centralizer_z1 h hz₁ hz₁z hord
          (Subgroup.mem_inf.mp hgN).2 hgz₁ he }

private lemma lemma54_blackB (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (σ τG : G)
    (hσ : σ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (hτG : τG = (τ : G)) :
    Lemma54BlackB z z₁ σ τG := by
  cases hσ
  cases hτG
  exact
    { hO2O3disj := disjoint_lemma54O2_lemma54O3 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
        hqτ hτ hτ₁ hτ₂
      hO2ncard := ncard_lemma54O2 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hO3ncard := ncard_lemma54O3 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hO2trans := exists_conj_eq_of_mem_lemma54O2 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
        hqτ hτ hτ₁ hτ₂
      hO2inv := fun c hc =>
        conj_mem_lemma54O2 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hc
      hO2mulz := mul_z_mem_lemma54O2 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hgen0 := by
        simpa using
          J_inf_lemma54W_le_closure (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      hO2orO3 := by
        intro a haW haJ
        simpa using
          mem_lemma54O2_or_mem_lemma54O3 (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
            haW haJ
      hexistsLabel := by
        intro x hxW hxJ
        simpa using
          exists_isLemma54Label (D := D) h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hxW hxJ }

private lemma lemma54_context [DecidableEq G]
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (σ τG ℓ₀ lam μ : G)
    (hσ : σ = ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) (hτG : τG = (τ : G))
    (hℓ₀ : ℓ₀ = 1 ∨ ℓ₀ = z) (hlam : lam = 1 ∨ lam = z₁)
    (hlabel : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
      ∀ x e, IsLemma54Label (z := z) σ τG x e →
        IsLemma54Label (z := z) σ τG (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹)))
    (hkey : ∀ g ∈ lemma54N₀ (z := z) σ τG, g ∉ centralizer ({z₁} : Set G) →
      ℓ₀ * (g * lam * g⁻¹) = lam * z)
    (hμN : μ ∈ lemma54N₀ (z := z) σ τG) (hμz₁ : μ ∉ centralizer ({z₁} : Set G))
    (hμH : μ ∈ H z) (hμz : μ * z * μ⁻¹ = z) (hμz₁' : μ * z₁ * μ⁻¹ = z₁ * z) :
    Lemma54Context z z₁ σ τG ℓ₀ lam μ :=
  { basic := lemma54_basic (D := D) h hz₁ hz₁z hord hqτ σ τG ℓ₀ lam μ hτG hℓ₀ hlam hlabel hkey
      hμN hμz₁ hμH hμz hμz₁'
    blackA := lemma54_blackA (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ σ τG hσ hτG
    blackB := lemma54_blackB (D := D) h hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ σ τG hσ hτG }

private lemma lemma54_lam_mem {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : lam ∈ centerIn (J z) := by
  rcases C.basic.hlam with h | h
  · rw [h]; exact Subgroup.one_mem _
  · rw [h]; exact C.blackA.hz₁

private lemma lemma54_lamz_mem {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : lam * z ∈ centerIn (J z) :=
  (centerIn (J z)).mul_mem (lemma54_lam_mem C) C.blackA.hzC

private lemma lemma54_lamz₁_mem {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : lam * z₁ ∈ centerIn (J z) :=
  (centerIn (J z)).mul_mem (lemma54_lam_mem C) C.blackA.hz₁

private lemma lemma54_lamz₁z_mem {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : lam * z₁ * z ∈ centerIn (J z) :=
  (centerIn (J z)).mul_mem (lemma54_lamz₁_mem C) C.blackA.hzC

private lemma lemma54_hO0 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (_C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lemma54OrbitFamily z σ τG z₁ lam 0 = {z} := rfl

private lemma lemma54_hO1 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (_C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lemma54OrbitFamily z σ τG z₁ lam 1 = {z₁, z₁ * z} := rfl

private theorem lemma54_hJ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i, a ∈ J z := by
  intro i hi a ha
  fin_cases i
  · change a ∈ ({z} : Finset G) at ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact C.blackA.hzJ
  · change a ∈ ({z₁, z₁ * z} : Finset G) at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · subst ha; exact C.blackA.hz₁J
    · subst ha; exact (J z).mul_mem C.blackA.hz₁J C.blackA.hzJ
  · change a ∈ lemma54O2F z σ τG at ha
    exact (C.blackA.hO2mem a (mem_lemma54O2F.mp ha)).2.1
  · change a ∈ lemma54O3F z σ τG z₁ at ha
    exact (C.blackA.hO3mem a (mem_lemma54O3F.mp ha)).2.1
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)

private theorem lemma54_hnJ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i, a ∉ J z := by
  intro i hi a ha
  fin_cases i
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (C.blackA.hmemW (lemma54_lam_mem C) (mem_lemma54OuterF.mp ha)).2
    · exact (C.blackA.hmemW (lemma54_lamz_mem C) (mem_lemma54OuterF.mp ha)).2
  · change a ∈ lemma54OuterF z σ τG (lam * z₁) at ha
    exact (C.blackA.hmemW (lemma54_lamz₁_mem C) (mem_lemma54OuterF.mp ha)).2
  · change a ∈ lemma54OuterF z σ τG (lam * z₁ * z) at ha
    exact (C.blackA.hmemW (lemma54_lamz₁z_mem C) (mem_lemma54OuterF.mp ha)).2

private theorem lemma54_hO2z [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam 2, a * z ∈ lemma54OrbitFamily z σ τG z₁ lam 2 := by
  intro a ha
  change a ∈ lemma54O2F z σ τG at ha
  change a * z ∈ lemma54O2F z σ τG
  exact mem_lemma54O2F.mpr (C.blackB.hO2mulz.1 a (mem_lemma54O2F.mp ha))

private theorem lemma54_hO3z [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam 3, a * z ∈ lemma54OrbitFamily z σ τG z₁ lam 3 := by
  intro a ha
  change a ∈ lemma54O3F z σ τG z₁ at ha
  change a * z ∈ lemma54O3F z σ τG z₁
  exact mem_lemma54O3F.mpr (C.blackB.hO2mulz.2 a (mem_lemma54O3F.mp ha))

private theorem lemma54_hOW [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i, ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i, a ∈ lemma54W z σ τG ∧ a ≠ 1 := by
  intro i a ha
  fin_cases i
  · change a ∈ ({z} : Finset G) at ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact ⟨C.blackA.hzW, C.basic.hz_ne_one⟩
  · change a ∈ ({z₁, z₁ * z} : Finset G) at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · subst ha
      exact ⟨Subgroup.mem_sup_left (C.blackA.hcenter_le C.blackA.hz₁),
        C.basic.hz₁_ne_one⟩
    · subst ha
      exact ⟨Subgroup.mem_sup_left (C.blackA.hcenter_le
        ((centerIn (J z)).mul_mem C.blackA.hz₁ C.blackA.hzC)), C.basic.hz₁z_ne_one⟩
  · change a ∈ lemma54O2F z σ τG at ha
    exact ⟨(C.blackA.hO2mem a (mem_lemma54O2F.mp ha)).1,
      fun h1 => (C.blackA.hO2mem a (mem_lemma54O2F.mp ha)).2.2 (h1 ▸ Subgroup.one_mem _)⟩
  · change a ∈ lemma54O3F z σ τG z₁ at ha
    exact ⟨(C.blackA.hO3mem a (mem_lemma54O3F.mp ha)).1,
      fun h1 => (C.blackA.hO3mem a (mem_lemma54O3F.mp ha)).2.2 (h1 ▸ Subgroup.one_mem _)⟩
  · change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact ⟨(C.blackA.hmemW (lemma54_lam_mem C) (mem_lemma54OuterF.mp ha)).1,
        fun h1 => (C.blackA.hmemW (lemma54_lam_mem C) (mem_lemma54OuterF.mp ha)).2
          (h1 ▸ Subgroup.one_mem _)⟩
    · exact ⟨(C.blackA.hmemW (lemma54_lamz_mem C) (mem_lemma54OuterF.mp ha)).1,
        fun h1 => (C.blackA.hmemW (lemma54_lamz_mem C) (mem_lemma54OuterF.mp ha)).2
          (h1 ▸ Subgroup.one_mem _)⟩
  · change a ∈ lemma54OuterF z σ τG (lam * z₁) at ha
    exact ⟨(C.blackA.hmemW (lemma54_lamz₁_mem C) (mem_lemma54OuterF.mp ha)).1,
      fun h1 => (C.blackA.hmemW (lemma54_lamz₁_mem C) (mem_lemma54OuterF.mp ha)).2
        (h1 ▸ Subgroup.one_mem _)⟩
  · change a ∈ lemma54OuterF z σ τG (lam * z₁ * z) at ha
    exact ⟨(C.blackA.hmemW (lemma54_lamz₁z_mem C) (mem_lemma54OuterF.mp ha)).1,
      fun h1 => (C.blackA.hmemW (lemma54_lamz₁z_mem C) (mem_lemma54OuterF.mp ha)).2
        (h1 ▸ Subgroup.one_mem _)⟩

private lemma lemma54_hO2coe [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (_C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (lemma54OrbitFamily z σ τG z₁ lam 2 : Set G) = lemma54O2 (z := z) σ τG := by
  rw [show lemma54OrbitFamily z σ τG z₁ lam 2 = lemma54O2F z σ τG from rfl]
  exact (Set.toFinite (lemma54O2 (z := z) σ τG)).coe_toFinset

private lemma lemma54_hO3coe [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (_C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (lemma54OrbitFamily z σ τG z₁ lam 3 : Set G) = lemma54O3 (z := z) σ τG z₁ := by
  rw [show lemma54OrbitFamily z σ τG z₁ lam 3 = lemma54O3F z σ τG z₁ from rfl]
  exact (Set.toFinite (lemma54O3 (z := z) σ τG z₁)).coe_toFinset

private theorem lemma54_hgen [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    J z ⊓ lemma54W z σ τG ≤ Subgroup.closure
      ((lemma54OrbitFamily z σ τG z₁ lam 2 : Set G) ∪
        (lemma54OrbitFamily z σ τG z₁ lam 3 : Set G)) := by
  rw [lemma54_hO2coe C, lemma54_hO3coe C]
  exact C.blackB.hgen0

private theorem lemma54_hmap_one [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∃ i : Fin 7, 4 ≤ (i : ℕ) ∧ ∀ a, IsLemma54Label (z := z) σ τG a 1 →
      a ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  rcases C.basic.hlam with hl1 | hlz
  · refine ⟨4, by norm_num, ?_⟩
    intro a ha
    change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z)
    rw [hl1]
    exact Finset.mem_union_left _ (mem_lemma54OuterF.mpr ha)
  · refine ⟨5, by norm_num, ?_⟩
    intro a ha
    change a ∈ lemma54OuterF z σ τG (lam * z₁)
    rw [hlz, C.basic.hz₁sq]
    exact mem_lemma54OuterF.mpr ha

private theorem lemma54_hmap_z [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∃ i : Fin 7, 4 ≤ (i : ℕ) ∧ ∀ a, IsLemma54Label (z := z) σ τG a z →
      a ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  rcases C.basic.hlam with hl1 | hlz
  · refine ⟨4, by norm_num, ?_⟩
    intro a ha
    change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z)
    rw [hl1]
    exact Finset.mem_union_right _
      (by simpa only [one_mul] using mem_lemma54OuterF.mpr ha)
  · refine ⟨6, by norm_num, ?_⟩
    intro a ha
    change a ∈ lemma54OuterF z σ τG (lam * z₁ * z)
    rw [hlz, C.basic.hz₁sq]
    exact by simpa only [one_mul] using mem_lemma54OuterF.mpr ha

private theorem lemma54_hmap_z1 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∃ i : Fin 7, 4 ≤ (i : ℕ) ∧ ∀ a, IsLemma54Label (z := z) σ τG a z₁ →
      a ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  rcases C.basic.hlam with hl1 | hlz
  · refine ⟨5, by norm_num, ?_⟩
    intro a ha
    change a ∈ lemma54OuterF z σ τG (lam * z₁)
    rw [hl1]
    exact by simpa only [one_mul] using mem_lemma54OuterF.mpr ha
  · refine ⟨4, by norm_num, ?_⟩
    intro a ha
    change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z)
    rw [hlz]
    exact Finset.mem_union_left _ (mem_lemma54OuterF.mpr ha)

private theorem lemma54_hmap_zz1 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∃ i : Fin 7, 4 ≤ (i : ℕ) ∧ ∀ a, IsLemma54Label (z := z) σ τG a (z * z₁) →
      a ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  rcases C.basic.hlam with hl1 | hlz
  · refine ⟨6, by norm_num, ?_⟩
    intro a ha
    rw [C.basic.hzz₁] at ha
    change a ∈ lemma54OuterF z σ τG (lam * z₁ * z)
    rw [hl1]
    exact by simpa only [one_mul] using mem_lemma54OuterF.mpr ha
  · refine ⟨4, by norm_num, ?_⟩
    intro a ha
    rw [C.basic.hzz₁] at ha
    change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z)
    rw [hlz]
    exact Finset.mem_union_right _ (mem_lemma54OuterF.mpr ha)

private theorem lemma54_hmap [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ e ∈ centerIn (J z), ∃ i : Fin 7, 4 ≤ (i : ℕ) ∧
      ∀ a, IsLemma54Label (z := z) σ τG a e →
        a ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  intro e he
  rcases C.blackA.hmem_centerIn_J he with h1 | h2 | h3 | h4
  · subst e; exact lemma54_hmap_one C
  · subst e; exact lemma54_hmap_z C
  · subst e; exact lemma54_hmap_z1 C
  · subst e; exact lemma54_hmap_zz1 C

private theorem lemma54_hcover [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ a ∈ lemma54W z σ τG, a ≠ 1 → ∃ i, a ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  intro a haW ha1
  by_cases haJ : a ∈ J z
  · rcases C.blackB.hO2orO3 a haW haJ with rfl | rfl | rfl | rfl | haO2 | haO3
    · exact absurd rfl ha1
    · exact ⟨0, by rw [lemma54_hO0 C]; simp⟩
    · exact ⟨1, by rw [lemma54_hO1 C]; simp⟩
    · exact ⟨1, by rw [lemma54_hO1 C]; simp⟩
    · exact ⟨2, by change a ∈ lemma54O2F z σ τG; exact mem_lemma54O2F.mpr haO2⟩
    · exact ⟨3, by change a ∈ lemma54O3F z σ τG z₁; exact mem_lemma54O3F.mpr haO3⟩
  · obtain ⟨e, he, hae⟩ := C.blackB.hexistsLabel a haW haJ
    obtain ⟨i, -, hmem⟩ := lemma54_hmap C e he
    exact ⟨i, hmem a hae⟩

private theorem lemma54_hcard_0_1 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (lemma54OrbitFamily z σ τG z₁ lam 0).card = lemma54Sizes 0 ∧
      (lemma54OrbitFamily z σ τG z₁ lam 1).card = lemma54Sizes 1 := by
  constructor
  · rw [lemma54_hO0 C]
    change ({z} : Finset G).card = 1
    rfl
  · rw [lemma54_hO1 C]
    change ({z₁, z₁ * z} : Finset G).card = 2
    rw [Finset.card_pair_eq_two_iff]
    exact fun h => C.basic.hz_ne_one (by
      have h1 := congrArg (fun x => z₁⁻¹ * x) h
      simpa [mul_assoc] using h1.symm)

private theorem lemma54_hcard_2_3 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (lemma54OrbitFamily z σ τG z₁ lam 2).card = lemma54Sizes 2 ∧
      (lemma54OrbitFamily z σ τG z₁ lam 3).card = lemma54Sizes 3 := by
  constructor
  · change (lemma54O2F z σ τG).card = 6
    rw [lemma54O2F, ← Set.ncard_eq_toFinset_card (lemma54O2 (z := z) σ τG)
      (Set.toFinite _)]
    exact C.blackB.hO2ncard
  · change (lemma54O3F z σ τG z₁).card = 6
    rw [lemma54O3F, ← Set.ncard_eq_toFinset_card (lemma54O3 (z := z) σ τG z₁)
      (Set.toFinite _)]
    exact C.blackB.hO3ncard

private theorem lemma54_hcard_4 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (lemma54OrbitFamily z σ τG z₁ lam 4).card = lemma54Sizes 4 := by
  change (lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z)).card = 8
  have hdisj : Disjoint (lemma54OuterF z σ τG lam) (lemma54OuterF z σ τG (lam * z)) := by
    rw [show lemma54OuterF z σ τG lam = (lemma54Outer z σ τG lam).toFinite.toFinset from rfl,
      show lemma54OuterF z σ τG (lam * z) =
        (lemma54Outer z σ τG (lam * z)).toFinite.toFinset from rfl,
      Set.Finite.disjoint_toFinset]
    exact disjoint_outer (σ := σ) (τ := τG) C.blackA.hunique
      (lemma54_lam_mem C) (lemma54_lamz_mem C) (fun h => C.basic.hz_ne_one (by
        have h1 := congrArg (fun x => lam⁻¹ * x) h
        simpa [mul_assoc] using h1.symm))
  rw [Finset.card_union_of_disjoint hdisj,
    C.blackA.hOuterCard lam (lemma54_lam_mem C),
    C.blackA.hOuterCard (lam * z) (lemma54_lamz_mem C)]

private theorem lemma54_hcard_5_6 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (lemma54OrbitFamily z σ τG z₁ lam 5).card = lemma54Sizes 5 ∧
      (lemma54OrbitFamily z σ τG z₁ lam 6).card = lemma54Sizes 6 := by
  constructor
  · change (lemma54OuterF z σ τG (lam * z₁)).card = 4
    exact C.blackA.hOuterCard (lam * z₁) (lemma54_lamz₁_mem C)
  · change (lemma54OuterF z σ τG (lam * z₁ * z)).card = 4
    exact C.blackA.hOuterCard (lam * z₁ * z) (lemma54_lamz₁z_mem C)

private theorem lemma54_hcard [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i, (lemma54OrbitFamily z σ τG z₁ lam i).card = lemma54Sizes i := by
  intro i
  fin_cases i
  · exact (lemma54_hcard_0_1 C).1
  · exact (lemma54_hcard_0_1 C).2
  · exact (lemma54_hcard_2_3 C).1
  · exact (lemma54_hcard_2_3 C).2
  · exact lemma54_hcard_4 C
  · exact (lemma54_hcard_5_6 C).1
  · exact (lemma54_hcard_5_6 C).2

private lemma lemma54_disjoint_of_subset_not {s t : Finset G} {A : Set G}
    (hs : ∀ x ∈ s, x ∈ A) (ht : ∀ x ∈ t, x ∉ A) : Disjoint s t := by
  rw [Finset.disjoint_left]
  intro x hx hy
  exact ht x hy (hs x hx)

private lemma lemma54_O0sub [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 0, x ∈ centerIn (J z) := by
  intro x hx
  rw [lemma54_hO0 C] at hx
  simp only [Finset.mem_singleton] at hx
  rw [hx]
  exact C.blackA.hzC

private lemma lemma54_O1sub [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 1, x ∈ centerIn (J z) := by
  intro x hx
  rw [lemma54_hO1 C] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact C.blackA.hz₁
  · exact (centerIn (J z)).mul_mem C.blackA.hz₁ C.blackA.hzC

private lemma lemma54_O0J [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 0, x ∈ J z := fun x hx =>
  (Subgroup.mem_inf.mp (lemma54_O0sub C x hx)).1

private lemma lemma54_O1J [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 1, x ∈ J z := fun x hx =>
  (Subgroup.mem_inf.mp (lemma54_O1sub C x hx)).1

private lemma lemma54_O2J [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 2, x ∈ J z := by
  intro x hx
  change x ∈ lemma54O2F z σ τG at hx
  exact (C.blackA.hO2mem x (mem_lemma54O2F.mp hx)).2.1

private lemma lemma54_O3J [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 3, x ∈ J z := by
  intro x hx
  change x ∈ lemma54O3F z σ τG z₁ at hx
  exact (C.blackA.hO3mem x (mem_lemma54O3F.mp hx)).2.1

private lemma lemma54_O2nZ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 2, x ∉ centerIn (J z) := by
  intro x hx
  change x ∈ lemma54O2F z σ τG at hx
  exact (C.blackA.hO2mem x (mem_lemma54O2F.mp hx)).2.2

private lemma lemma54_O3nZ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 3, x ∉ centerIn (J z) := by
  intro x hx
  change x ∈ lemma54O3F z σ τG z₁ at hx
  exact (C.blackA.hO3mem x (mem_lemma54O3F.mp hx)).2.2

private lemma lemma54_O4nJ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 4, x ∉ J z := by
  intro x hx
  change x ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (C.blackA.hmemW (lemma54_lam_mem C) (mem_lemma54OuterF.mp hx)).2
  · exact (C.blackA.hmemW (lemma54_lamz_mem C) (mem_lemma54OuterF.mp hx)).2

private lemma lemma54_O5nJ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 5, x ∉ J z := by
  intro x hx
  change x ∈ lemma54OuterF z σ τG (lam * z₁) at hx
  exact (C.blackA.hmemW (lemma54_lamz₁_mem C) (mem_lemma54OuterF.mp hx)).2

private lemma lemma54_O6nJ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ x ∈ lemma54OrbitFamily z σ τG z₁ lam 6, x ∉ J z := by
  intro x hx
  change x ∈ lemma54OuterF z σ τG (lam * z₁ * z) at hx
  exact (C.blackA.hmemW (lemma54_lamz₁z_mem C) (mem_lemma54OuterF.mp hx)).2

private lemma lemma54_OuterDisj [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ {e e' : G}, e ∈ centerIn (J z) → e' ∈ centerIn (J z) → e ≠ e' →
      Disjoint (lemma54OuterF z σ τG e) (lemma54OuterF z σ τG e') := by
  intro e e' he he' hne
  rw [show lemma54OuterF z σ τG e = (lemma54Outer z σ τG e).toFinite.toFinset from rfl,
    show lemma54OuterF z σ τG e' = (lemma54Outer z σ τG e').toFinite.toFinset from rfl,
    Set.Finite.disjoint_toFinset]
  exact disjoint_outer (σ := σ) (τ := τG) C.blackA.hunique he he' hne

private lemma lemma54_z_z₁ {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : z ≠ z₁ :=
  fun h => C.blackA.hz₁z (h ▸ Subgroup.mem_zpowers z)

private lemma lemma54_z_z₁z {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : z ≠ z₁ * z := by
  intro h
  apply C.basic.hz₁_ne_one
  have h1 := congrArg (fun x => x * z⁻¹) h
  simpa [mul_assoc, C.basic.hz2] using h1.symm

private lemma lemma54_lam_ne_lamz {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) : lam ≠ lam * z := by
  intro h
  have h1 : (1 : G) = z := by
    have := congrArg (fun x => lam⁻¹ * x) h
    simpa [mul_assoc] using this
  exact C.basic.hz_ne_one h1.symm

private lemma lemma54_lam_ne_lamz₁ {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lam ≠ lam * z₁ := by
  intro h
  have h1 : (1 : G) = z₁ := by
    have := congrArg (fun x => lam⁻¹ * x) h
    simpa [mul_assoc] using this
  exact C.basic.hz₁_ne_one h1.symm

private lemma lemma54_lam_ne_lamz₁z {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lam ≠ lam * z₁ * z := by
  intro h
  have h1 : (1 : G) = z₁ * z := by
    have := congrArg (fun x => lam⁻¹ * x) h
    simpa [mul_assoc] using this
  exact C.basic.hz₁z_ne_one h1.symm

private lemma lemma54_lamz_ne_lamz₁ {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lam * z ≠ lam * z₁ := by
  intro h
  have h1 : z = z₁ := by
    have := congrArg (fun x => lam⁻¹ * x) h
    simpa [mul_assoc] using this
  exact lemma54_z_z₁ C h1

private lemma lemma54_lamz_ne_lamz₁z {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lam * z ≠ lam * z₁ * z := by
  intro h
  have h1 : z = z₁ * z := by
    have := congrArg (fun x => lam⁻¹ * x) h
    simpa [mul_assoc] using this
  exact lemma54_z_z₁z C h1

private lemma lemma54_lamz₁_ne_lamz₁z {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    lam * z₁ ≠ lam * z₁ * z := by
  intro h
  have h1 : (1 : G) = z := by
    have := congrArg (fun x => (lam * z₁)⁻¹ * x) h
    simpa [mul_assoc] using this
  exact C.basic.hz_ne_one h1.symm

private lemma lemma54_disjoint_h01 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    Disjoint (lemma54OrbitFamily z σ τG z₁ lam 0) (lemma54OrbitFamily z σ τG z₁ lam 1) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [lemma54_hO0 C] at hx
  rw [lemma54_hO1 C] at hy
  simp only [Finset.mem_singleton] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  subst hx
  rcases hy with h | h
  · exact lemma54_z_z₁ C h
  · exact lemma54_z_z₁z C h

private lemma lemma54_disjoint_h23 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    Disjoint (lemma54OrbitFamily z σ τG z₁ lam 2) (lemma54OrbitFamily z σ τG z₁ lam 3) := by
  rw [show lemma54OrbitFamily z σ τG z₁ lam 2 = lemma54O2F z σ τG from rfl,
    show lemma54OrbitFamily z σ τG z₁ lam 3 = lemma54O3F z σ τG z₁ from rfl,
    lemma54O2F, lemma54O3F, Set.Finite.disjoint_toFinset]
  exact C.blackB.hO2O3disj

private lemma lemma54_disjoint_h45 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    Disjoint (lemma54OrbitFamily z σ τG z₁ lam 4) (lemma54OrbitFamily z σ τG z₁ lam 5) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  change x ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at hx
  change x ∈ lemma54OuterF z σ τG (lam * z₁) at hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (Finset.disjoint_left.mp (lemma54_OuterDisj C (lemma54_lam_mem C)
      (lemma54_lamz₁_mem C) (lemma54_lam_ne_lamz₁ C)) hx) hy
  · exact (Finset.disjoint_left.mp (lemma54_OuterDisj C (lemma54_lamz_mem C)
      (lemma54_lamz₁_mem C) (lemma54_lamz_ne_lamz₁ C)) hx) hy

private lemma lemma54_disjoint_h46 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    Disjoint (lemma54OrbitFamily z σ τG z₁ lam 4) (lemma54OrbitFamily z σ τG z₁ lam 6) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  change x ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at hx
  change x ∈ lemma54OuterF z σ τG (lam * z₁ * z) at hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (Finset.disjoint_left.mp (lemma54_OuterDisj C (lemma54_lam_mem C)
      (lemma54_lamz₁z_mem C) (lemma54_lam_ne_lamz₁z C)) hx) hy
  · exact (Finset.disjoint_left.mp (lemma54_OuterDisj C (lemma54_lamz_mem C)
      (lemma54_lamz₁z_mem C) (lemma54_lamz_ne_lamz₁z C)) hx) hy

private lemma lemma54_disjoint_h56 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    Disjoint (lemma54OrbitFamily z σ τG z₁ lam 5) (lemma54OrbitFamily z σ τG z₁ lam 6) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  change x ∈ lemma54OuterF z σ τG (lam * z₁) at hx
  change x ∈ lemma54OuterF z σ τG (lam * z₁ * z) at hy
  exact (Finset.disjoint_left.mp (lemma54_OuterDisj C (lemma54_lamz₁_mem C)
    (lemma54_lamz₁z_mem C) (lemma54_lamz₁_ne_lamz₁z C)) hx) hy

private theorem lemma54_disjoint_low [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i j : Fin 7, (i : ℕ) < 4 → (j : ℕ) < 4 → i ≠ j →
      Disjoint (lemma54OrbitFamily z σ τG z₁ lam i) (lemma54OrbitFamily z σ τG z₁ lam j) := by
  intro i j hi hj hij
  fin_cases i
  · fin_cases j
    · exact absurd rfl hij
    · exact lemma54_disjoint_h01 C
    · exact lemma54_disjoint_of_subset_not (lemma54_O0sub C) (lemma54_O2nZ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O0sub C) (lemma54_O3nZ C)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
  · fin_cases j
    · exact (lemma54_disjoint_h01 C).symm
    · exact absurd rfl hij
    · exact lemma54_disjoint_of_subset_not (lemma54_O1sub C) (lemma54_O2nZ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O1sub C) (lemma54_O3nZ C)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
  · fin_cases j
    · exact (lemma54_disjoint_of_subset_not (lemma54_O0sub C) (lemma54_O2nZ C)).symm
    · exact (lemma54_disjoint_of_subset_not (lemma54_O1sub C) (lemma54_O2nZ C)).symm
    · exact absurd rfl hij
    · exact lemma54_disjoint_h23 C
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
  · fin_cases j
    · exact (lemma54_disjoint_of_subset_not (lemma54_O0sub C) (lemma54_O3nZ C)).symm
    · exact (lemma54_disjoint_of_subset_not (lemma54_O1sub C) (lemma54_O3nZ C)).symm
    · exact (lemma54_disjoint_h23 C).symm
    · exact absurd rfl hij
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)

private theorem lemma54_disjoint_low_high [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i j : Fin 7, (i : ℕ) < 4 → 4 ≤ (j : ℕ) → i ≠ j →
      Disjoint (lemma54OrbitFamily z σ τG z₁ lam i) (lemma54OrbitFamily z σ τG z₁ lam j) := by
  intro i j hi hj hij
  fin_cases i
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact lemma54_disjoint_of_subset_not (lemma54_O0J C) (lemma54_O4nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O0J C) (lemma54_O5nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O0J C) (lemma54_O6nJ C)
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact lemma54_disjoint_of_subset_not (lemma54_O1J C) (lemma54_O4nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O1J C) (lemma54_O5nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O1J C) (lemma54_O6nJ C)
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact lemma54_disjoint_of_subset_not (lemma54_O2J C) (lemma54_O4nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O2J C) (lemma54_O5nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O2J C) (lemma54_O6nJ C)
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact lemma54_disjoint_of_subset_not (lemma54_O3J C) (lemma54_O4nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O3J C) (lemma54_O5nJ C)
    · exact lemma54_disjoint_of_subset_not (lemma54_O3J C) (lemma54_O6nJ C)
  · exact absurd hi (by norm_num : ¬ (4 : ℕ) < 4)
  · exact absurd hi (by norm_num : ¬ (5 : ℕ) < 4)
  · exact absurd hi (by norm_num : ¬ (6 : ℕ) < 4)

private theorem lemma54_disjoint_high [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i j : Fin 7, 4 ≤ (i : ℕ) → 4 ≤ (j : ℕ) → i ≠ j →
      Disjoint (lemma54OrbitFamily z σ τG z₁ lam i) (lemma54OrbitFamily z σ τG z₁ lam j) := by
  intro i j hi hj hij
  fin_cases i
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd rfl hij
    · exact lemma54_disjoint_h45 C
    · exact lemma54_disjoint_h46 C
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact (lemma54_disjoint_h45 C).symm
    · exact absurd rfl hij
    · exact lemma54_disjoint_h56 C
  · fin_cases j
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact absurd hj (by norm_num)
    · exact (lemma54_disjoint_h46 C).symm
    · exact (lemma54_disjoint_h56 C).symm
    · exact absurd rfl hij

private theorem lemma54_hdisj [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i j, i ≠ j → Disjoint (lemma54OrbitFamily z σ τG z₁ lam i)
      (lemma54OrbitFamily z σ τG z₁ lam j) := by
  intro i j hij
  by_cases hi : (i : ℕ) < 4
  · by_cases hj : (j : ℕ) < 4
    · exact lemma54_disjoint_low C i j hi hj hij
    · exact lemma54_disjoint_low_high C i j hi (by omega) hij
  · by_cases hj : (j : ℕ) < 4
    · exact (lemma54_disjoint_low_high C j i hj (by omega) (fun h => hij h.symm)).symm
    · exact lemma54_disjoint_high C i j (by omega) (by omega) hij

private lemma lemma54_heqμ [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    (ℓ₀ * (μ * (lam * z) * μ⁻¹) = lam) ∧
      (ℓ₀ * (μ * (lam * z₁) * μ⁻¹) = lam * z₁) ∧
      (ℓ₀ * (μ * (lam * z₁ * z) * μ⁻¹) = lam * z₁ * z) :=
  outer_label_equations (C.basic.hkey μ C.basic.hμN C.basic.hμz₁)
    C.basic.hμz C.basic.hμz₁' C.basic.hz2 C.basic.hzz₁

private theorem lemma54_horb_J [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      ∀ b ∈ lemma54OrbitFamily z σ τG z₁ lam i,
        ∃ c ∈ lemma54N₀ (z := z) σ τG, c * a * c⁻¹ = b := by
  intro i hi a ha b hb
  fin_cases i
  · change a ∈ ({z} : Finset G) at ha
    change b ∈ ({z} : Finset G) at hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b
    exact ⟨1, (lemma54N₀ (z := z) σ τG).one_mem, by simp⟩
  · change a ∈ ({z₁, z₁ * z} : Finset G) at ha
    change b ∈ ({z₁, z₁ * z} : Finset G) at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · subst a; subst b; exact ⟨1, (lemma54N₀ (z := z) σ τG).one_mem, by simp⟩
    · subst a; subst b; exact ⟨μ, C.basic.hμN, C.basic.hμz₁'⟩
    · subst a; subst b
      refine ⟨μ, C.basic.hμN, ?_⟩
      calc μ * (z₁ * z) * μ⁻¹ = (μ * z₁ * μ⁻¹) * (μ * z * μ⁻¹) := by group
        _ = (z₁ * z) * z := by rw [C.basic.hμz₁', C.basic.hμz]
        _ = z₁ := by rw [mul_assoc, C.basic.hz2, mul_one]
    · subst a; subst b; exact ⟨1, (lemma54N₀ (z := z) σ τG).one_mem, by simp⟩
  · change a ∈ lemma54O2F z σ τG at ha
    change b ∈ lemma54O2F z σ τG at hb
    exact C.blackB.hO2trans.1 a (mem_lemma54O2F.mp ha) b (mem_lemma54O2F.mp hb)
  · change a ∈ lemma54O3F z σ τG z₁ at ha
    change b ∈ lemma54O3F z σ τG z₁ at hb
    exact C.blackB.hO2trans.2 a (mem_lemma54O3F.mp ha) b (mem_lemma54O3F.mp hb)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)

private theorem lemma54_horb_outer [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      ∀ b ∈ lemma54OrbitFamily z σ τG z₁ lam i,
        ∃ c ∈ lemma54N₀ (z := z) σ τG, c * a * c⁻¹ = b := by
  intro i hi a ha b hb
  fin_cases i
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at ha
    change b ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at hb
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact exists_conj_eq_of_mem_outer (σ := σ) (τ := τG) (N := lemma54N₀ (z := z) σ τG)
        (lemma54_lam_mem C) C.blackA.hQN (mem_lemma54OuterF.mp ha) (mem_lemma54OuterF.mp hb)
    · have hμa : IsLemma54Label (z := z) σ τG (μ * a * μ⁻¹) (lam * z) :=
        isLemma54Label_conj_of_not_mem_centralizer C.basic.hlabel C.basic.hμN C.basic.hμz₁
          (C.basic.hkey μ C.basic.hμN C.basic.hμz₁) a (mem_lemma54OuterF.mp ha)
      obtain ⟨c, hcN, hcab⟩ := exists_conj_eq_of_mem_outer (σ := σ) (τ := τG)
        (N := lemma54N₀ (z := z) σ τG) (lemma54_lamz_mem C) C.blackA.hQN hμa
        (mem_lemma54OuterF.mp hb)
      refine ⟨c * μ, (lemma54N₀ (z := z) σ τG).mul_mem hcN C.basic.hμN, ?_⟩
      calc (c * μ) * a * (c * μ)⁻¹ = c * (μ * a * μ⁻¹) * c⁻¹ := by group
        _ = b := hcab
    · have hμa : IsLemma54Label (z := z) σ τG (μ * a * μ⁻¹) lam :=
        isLemma54Label_conj_of_not_mem_centralizer C.basic.hlabel C.basic.hμN C.basic.hμz₁
          (lemma54_heqμ C).1 a (mem_lemma54OuterF.mp ha)
      obtain ⟨c, hcN, hcab⟩ := exists_conj_eq_of_mem_outer (σ := σ) (τ := τG)
        (N := lemma54N₀ (z := z) σ τG) (lemma54_lam_mem C) C.blackA.hQN hμa
        (mem_lemma54OuterF.mp hb)
      refine ⟨c * μ, (lemma54N₀ (z := z) σ τG).mul_mem hcN C.basic.hμN, ?_⟩
      calc (c * μ) * a * (c * μ)⁻¹ = c * (μ * a * μ⁻¹) * c⁻¹ := by group
        _ = b := hcab
    · exact exists_conj_eq_of_mem_outer (σ := σ) (τ := τG) (N := lemma54N₀ (z := z) σ τG)
        (lemma54_lamz_mem C) C.blackA.hQN (mem_lemma54OuterF.mp ha) (mem_lemma54OuterF.mp hb)
  · change a ∈ lemma54OuterF z σ τG (lam * z₁) at ha
    change b ∈ lemma54OuterF z σ τG (lam * z₁) at hb
    exact exists_conj_eq_of_mem_outer (σ := σ) (τ := τG) (N := lemma54N₀ (z := z) σ τG)
      (lemma54_lamz₁_mem C) C.blackA.hQN (mem_lemma54OuterF.mp ha) (mem_lemma54OuterF.mp hb)
  · change a ∈ lemma54OuterF z σ τG (lam * z₁ * z) at ha
    change b ∈ lemma54OuterF z σ τG (lam * z₁ * z) at hb
    exact exists_conj_eq_of_mem_outer (σ := σ) (τ := τG) (N := lemma54N₀ (z := z) σ τG)
      (lemma54_lamz₁z_mem C) C.blackA.hQN (mem_lemma54OuterF.mp ha) (mem_lemma54OuterF.mp hb)

private theorem lemma54_horb [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i, ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      ∀ b ∈ lemma54OrbitFamily z σ τG z₁ lam i,
        ∃ c ∈ lemma54N₀ (z := z) σ τG, c * a * c⁻¹ = b := by
  intro i a ha b hb
  by_cases hi : (i : ℕ) < 4
  · exact lemma54_horb_J C i hi a ha b hb
  · exact lemma54_horb_outer C i (by omega) a ha b hb

private lemma lemma54_hswap [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) {g : G}
    (hgN : g ∈ lemma54N₀ (z := z) σ τG)
    (hgz₁ : g ∉ centralizer ({z₁} : Set G)) :
    (∀ a, IsLemma54Label (z := z) σ τG a lam →
      IsLemma54Label (z := z) σ τG (g * a * g⁻¹) (lam * z)) ∧
    (∀ a, IsLemma54Label (z := z) σ τG a (lam * z) →
      IsLemma54Label (z := z) σ τG (g * a * g⁻¹) lam) ∧
    (∀ a, IsLemma54Label (z := z) σ τG a (lam * z₁) →
      IsLemma54Label (z := z) σ τG (g * a * g⁻¹) (lam * z₁)) ∧
    (∀ a, IsLemma54Label (z := z) σ τG a (lam * z₁ * z) →
      IsLemma54Label (z := z) σ τG (g * a * g⁻¹) (lam * z₁ * z)) := by
  have hgH : g ∈ H z := (Subgroup.mem_inf.mp hgN).2
  have hcomm : g * z = z * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H_eq_centralizer] using hgH)
  have hgz : g * z * g⁻¹ = z := by rw [hcomm, mul_inv_cancel_right]
  have hgz₁' : g * z₁ * g⁻¹ = z₁ * z := C.blackA.hconjz₁ g hgH hgz₁
  have heq := outer_label_equations (C.basic.hkey g hgN hgz₁) hgz hgz₁' C.basic.hz2 C.basic.hzz₁
  exact ⟨fun a ha => isLemma54Label_conj_of_not_mem_centralizer C.basic.hlabel hgN hgz₁
      (C.basic.hkey g hgN hgz₁) a ha,
    fun a ha => isLemma54Label_conj_of_not_mem_centralizer C.basic.hlabel hgN hgz₁ heq.1 a ha,
    fun a ha => isLemma54Label_conj_of_not_mem_centralizer C.basic.hlabel hgN hgz₁ heq.2.1 a ha,
    fun a ha => isLemma54Label_conj_of_not_mem_centralizer C.basic.hlabel hgN hgz₁ heq.2.2 a ha⟩

private lemma lemma54_hfix [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) {g : G}
    (hgN : g ∈ lemma54N₀ (z := z) σ τG)
    (hgz₁ : g ∈ centralizer ({z₁} : Set G)) :
    ∀ e ∈ centerIn (J z), ∀ a, IsLemma54Label (z := z) σ τG a e →
      IsLemma54Label (z := z) σ τG (g * a * g⁻¹) e := by
  have hgH : g ∈ H z := (Subgroup.mem_inf.mp hgN).2
  have hgσ : g ∈ centralizer ({σ} : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hgN).1).2
  intro e he a ha
  exact isLemma54Label_conj_of_mem_centralizer hgH hgσ (C.blackA.hℓ1 g hgN hgz₁) he
    (C.blackA.heq_self_centerIn g hgN hgz₁ e he) ha

private theorem lemma54_hinv_J [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      ∀ c ∈ lemma54N₀ (z := z) σ τG,
        c * a * c⁻¹ ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  intro i hi a ha c hcN
  fin_cases i
  · change a ∈ ({z} : Finset G) at ha
    simp only [Finset.mem_singleton] at ha; subst a
    change c * z * c⁻¹ ∈ ({z} : Finset G)
    have hcH : c ∈ H z := (Subgroup.mem_inf.mp hcN).2
    have hcomm : c * z = z * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H_eq_centralizer] using hcH)
    have hcz : c * z * c⁻¹ = z := by rw [hcomm, mul_inv_cancel_right]
    rw [hcz]; simp
  · change a ∈ ({z₁, z₁ * z} : Finset G) at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    have hcH : c ∈ H z := (Subgroup.mem_inf.mp hcN).2
    have hcomm : c * z = z * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (by simpa [H_eq_centralizer] using hcH)
    have hcz : c * z * c⁻¹ = z := by rw [hcomm, mul_inv_cancel_right]
    by_cases hcz₁ : c ∈ centralizer ({z₁} : Set G)
    · have hcz₁' : c * z₁ * c⁻¹ = z₁ := C.blackA.heq_self_centerIn c hcN hcz₁ z₁ C.blackA.hz₁
      rcases ha with ha | ha
      · subst a; change c * z₁ * c⁻¹ ∈ ({z₁, z₁ * z} : Finset G)
        rw [hcz₁']; simp
      · subst a
        change c * (z₁ * z) * c⁻¹ ∈ ({z₁, z₁ * z} : Finset G)
        rw [conj_mul_eq_of_conj_eq hcz₁' hcz]; simp
    · have hcz₁' : c * z₁ * c⁻¹ = z₁ * z := C.blackA.hconjz₁ c hcH hcz₁
      rcases ha with ha | ha
      · subst a; change c * z₁ * c⁻¹ ∈ ({z₁, z₁ * z} : Finset G)
        rw [hcz₁']; simp
      · subst a
        change c * (z₁ * z) * c⁻¹ ∈ ({z₁, z₁ * z} : Finset G)
        have hczz : c * (z₁ * z) * c⁻¹ = z₁ := by
          calc c * (z₁ * z) * c⁻¹ = (c * z₁ * c⁻¹) * (c * z * c⁻¹) := by group
            _ = (z₁ * z) * z := by rw [hcz₁', hcz]
            _ = z₁ := by rw [mul_assoc, C.basic.hz2, mul_one]
        rw [hczz]; simp
  · change a ∈ lemma54O2F z σ τG at ha
    change c * a * c⁻¹ ∈ lemma54O2F z σ τG
    exact mem_lemma54O2F.mpr ((C.blackB.hO2inv c hcN).1 a (mem_lemma54O2F.mp ha))
  · change a ∈ lemma54O3F z σ τG z₁ at ha
    change c * a * c⁻¹ ∈ lemma54O3F z σ τG z₁
    exact mem_lemma54O3F.mpr ((C.blackB.hO2inv c hcN).2 a (mem_lemma54O3F.mp ha))
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)

private theorem lemma54_hinv_outer [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      ∀ c ∈ lemma54N₀ (z := z) σ τG,
        c * a * c⁻¹ ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  intro i hi a ha c hcN
  fin_cases i
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · exact absurd hi (by norm_num)
  · change a ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z) at ha
    change c * a * c⁻¹ ∈ lemma54OuterF z σ τG lam ∪ lemma54OuterF z σ τG (lam * z)
    rcases Finset.mem_union.mp ha with ha | ha
    · by_cases hcz₁ : c ∈ centralizer ({z₁} : Set G)
      · exact Finset.mem_union_left _
          (mem_lemma54OuterF.mpr (lemma54_hfix C hcN hcz₁ lam (lemma54_lam_mem C) a
            (mem_lemma54OuterF.mp ha)))
      · exact Finset.mem_union_right _
          (mem_lemma54OuterF.mpr ((lemma54_hswap C hcN hcz₁).1 a (mem_lemma54OuterF.mp ha)))
    · by_cases hcz₁ : c ∈ centralizer ({z₁} : Set G)
      · exact Finset.mem_union_right _
          (mem_lemma54OuterF.mpr (lemma54_hfix C hcN hcz₁ (lam * z) (lemma54_lamz_mem C) a
            (mem_lemma54OuterF.mp ha)))
      · exact Finset.mem_union_left _
          (mem_lemma54OuterF.mpr ((lemma54_hswap C hcN hcz₁).2.1 a (mem_lemma54OuterF.mp ha)))
  · change a ∈ lemma54OuterF z σ τG (lam * z₁) at ha
    change c * a * c⁻¹ ∈ lemma54OuterF z σ τG (lam * z₁)
    by_cases hcz₁ : c ∈ centralizer ({z₁} : Set G)
    · exact mem_lemma54OuterF.mpr (lemma54_hfix C hcN hcz₁ (lam * z₁) (lemma54_lamz₁_mem C) a
        (mem_lemma54OuterF.mp ha))
    · exact mem_lemma54OuterF.mpr ((lemma54_hswap C hcN hcz₁).2.2.1 a (mem_lemma54OuterF.mp ha))
  · change a ∈ lemma54OuterF z σ τG (lam * z₁ * z) at ha
    change c * a * c⁻¹ ∈ lemma54OuterF z σ τG (lam * z₁ * z)
    by_cases hcz₁ : c ∈ centralizer ({z₁} : Set G)
    · exact mem_lemma54OuterF.mpr (lemma54_hfix C hcN hcz₁ (lam * z₁ * z)
        (lemma54_lamz₁z_mem C) a (mem_lemma54OuterF.mp ha))
    · exact mem_lemma54OuterF.mpr ((lemma54_hswap C hcN hcz₁).2.2.2 a (mem_lemma54OuterF.mp ha))

private theorem lemma54_hinv [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ i, ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      ∀ c ∈ lemma54N₀ (z := z) σ τG,
        c * a * c⁻¹ ∈ lemma54OrbitFamily z σ τG z₁ lam i := by
  intro i a ha c hcN
  by_cases hi : (i : ℕ) < 4
  · exact lemma54_hinv_J C i hi a ha c hcN
  · exact lemma54_hinv_outer C i (by omega) a ha c hcN

private lemma lemma54_y_mem_H [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) {q₁ q₂ : G}
    (hq₁ : q₁ ∈ J z ⊓ centralizer ({σ} : Set G))
    (hq₂ : q₂ ∈ J z ⊓ centralizer ({σ} : Set G)) :
    q₁ * q₂⁻¹ * μ ∈ H z := by
  refine (H z).mul_mem ?_ C.basic.hμH
  exact (H z).mul_mem (J_le_H hq₁.1) ((H z).inv_mem (J_le_H hq₂.1))

private lemma lemma54_y_centralizes [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) {a e q₁ q₂ : G}
    (he : e ∈ centerIn (J z))
    (hq₁ : q₁ ∈ J z ⊓ centralizer ({σ} : Set G))
    (hq₂ : q₂ ∈ J z ⊓ centralizer ({σ} : Set G))
    (haeq : a = q₁ * τG * q₁⁻¹ * e)
    (hμaeq : μ * a * μ⁻¹ = q₂ * τG * q₂⁻¹ * e) :
    q₁ * q₂⁻¹ * μ ∈ centralizer ({a} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : (q₁ * q₂⁻¹ * μ) * a * (q₁ * q₂⁻¹ * μ)⁻¹ = a := by
    calc (q₁ * q₂⁻¹ * μ) * a * (q₁ * q₂⁻¹ * μ)⁻¹
        = (q₁ * q₂⁻¹) * (μ * a * μ⁻¹) * (q₁ * q₂⁻¹)⁻¹ := by group
      _ = (q₁ * q₂⁻¹) * (q₂ * τG * q₂⁻¹ * e) * (q₁ * q₂⁻¹)⁻¹ := by rw [hμaeq]
      _ = a := by
            rw [haeq]
            have hq₂e : q₂⁻¹ * e * q₂ = e := by
              simpa using conj_eq_self_of_mem_centerIn he ((J z).inv_mem hq₂.1)
            have hq₁e : q₁ * e * q₁⁻¹ = e := conj_eq_self_of_mem_centerIn he hq₁.1
            calc (q₁ * q₂⁻¹) * (q₂ * τG * q₂⁻¹ * e) * (q₁ * q₂⁻¹)⁻¹
                = q₁ * τG * (q₂⁻¹ * e * q₂) * q₁⁻¹ := by group
              _ = q₁ * τG * e * q₁⁻¹ := by rw [hq₂e]
              _ = q₁ * τG * q₁⁻¹ * e := by
                    have hcomm : e * q₁⁻¹ = q₁⁻¹ * e :=
                      (Subgroup.mem_centralizer_iff.mp he.2 q₁⁻¹
                        ((J z).inv_mem hq₁.1)).symm
                    calc q₁ * τG * e * q₁⁻¹ = q₁ * τG * (e * q₁⁻¹) := by group
                      _ = q₁ * τG * (q₁⁻¹ * e) := by rw [hcomm]
                      _ = q₁ * τG * q₁⁻¹ * e := by group
  calc (q₁ * q₂⁻¹ * μ) * a = ((q₁ * q₂⁻¹ * μ) * a * (q₁ * q₂⁻¹ * μ)⁻¹) *
        (q₁ * q₂⁻¹ * μ) := by group
    _ = a * (q₁ * q₂⁻¹ * μ) := by rw [hconj]

private lemma lemma54_y_not_centralizer [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) {q₁ q₂ : G}
    (hq₁ : q₁ ∈ J z ⊓ centralizer ({σ} : Set G))
    (hq₂ : q₂ ∈ J z ⊓ centralizer ({σ} : Set G)) :
    q₁ * q₂⁻¹ * μ ∉ centralizer ({z₁} : Set G) := by
  intro hyz₁
  have hcomm : (q₁ * q₂⁻¹ * μ) * z₁ = z₁ * (q₁ * q₂⁻¹ * μ) :=
    Subgroup.mem_centralizer_singleton_iff.mp hyz₁
  have hq₁z : q₁ * z * q₁⁻¹ = z :=
    conj_eq_self_of_mem_centerIn C.blackA.hzC hq₁.1
  have hq₂z : q₂ * z * q₂⁻¹ = z :=
    conj_eq_self_of_mem_centerIn C.blackA.hzC hq₂.1
  have hq₁z₁ : q₁ * z₁ * q₁⁻¹ = z₁ := conj_eq_self_of_mem_centerIn C.blackA.hz₁ hq₁.1
  have hq₂z₁ : q₂ * z₁ * q₂⁻¹ = z₁ := conj_eq_self_of_mem_centerIn C.blackA.hz₁ hq₂.1
  have hq₁zz₁ : q₁ * (z * z₁) * q₁⁻¹ = z * z₁ :=
    conj_mul_eq_of_conj_eq hq₁z hq₁z₁
  have hq₂zz₁ : q₂⁻¹ * (z * z₁) * q₂ = z * z₁ := by
    have hq₂z_inv : (q₂⁻¹) * z * (q₂⁻¹)⁻¹ = z :=
      conj_eq_self_of_mem_centerIn C.blackA.hzC ((J z).inv_mem hq₂.1)
    have hq₂z₁_inv : (q₂⁻¹) * z₁ * (q₂⁻¹)⁻¹ = z₁ :=
      conj_eq_self_of_mem_centerIn C.blackA.hz₁ ((J z).inv_mem hq₂.1)
    simpa using conj_mul_eq_of_conj_eq hq₂z_inv hq₂z₁_inv
  have hqconj : (q₁ * q₂⁻¹) * (z * z₁) * (q₁ * q₂⁻¹)⁻¹ = z * z₁ := by
    calc (q₁ * q₂⁻¹) * (z * z₁) * (q₁ * q₂⁻¹)⁻¹
        = q₁ * (q₂⁻¹ * (z * z₁) * q₂) * q₁⁻¹ := by group
      _ = q₁ * (z * z₁) * q₁⁻¹ := by rw [hq₂zz₁]
      _ = z * z₁ := hq₁zz₁
  have hqconj' : (q₁ * q₂⁻¹) * (z₁ * z) * (q₁ * q₂⁻¹)⁻¹ = z₁ * z := by
    simpa [C.basic.hzz₁] using hqconj
  have hconj : (q₁ * q₂⁻¹ * μ) * z₁ * (q₁ * q₂⁻¹ * μ)⁻¹ = z * z₁ := by
    calc (q₁ * q₂⁻¹ * μ) * z₁ * (q₁ * q₂⁻¹ * μ)⁻¹
        = (q₁ * q₂⁻¹) * (μ * z₁ * μ⁻¹) * (q₁ * q₂⁻¹)⁻¹ := by group
      _ = (q₁ * q₂⁻¹) * (z₁ * z) * (q₁ * q₂⁻¹)⁻¹ := by rw [C.basic.hμz₁']
      _ = z₁ * z := hqconj'
      _ = z * z₁ := C.basic.hzz₁.symm
  have hcontra : z * z₁ = z₁ := by
    rw [← hconj]
    calc (q₁ * q₂⁻¹ * μ) * z₁ * (q₁ * q₂⁻¹ * μ)⁻¹ = z₁ * (q₁ * q₂⁻¹ * μ) *
          (q₁ * q₂⁻¹ * μ)⁻¹ := by rw [hcomm]
      _ = z₁ := by group
  have hzne : z * z₁ ≠ z₁ := by
    intro h
    have hz : z = 1 := by
      have h1 := congrArg (fun x => x * z₁⁻¹) h
      simpa [mul_assoc] using h1
    exact C.basic.hz_ne_one hz
  exact hzne hcontra

private theorem lemma54_hO56_aux [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) {a e : G}
    (he : e ∈ centerIn (J z))
    (hμe : ∀ x, IsLemma54Label (z := z) σ τG x e →
      IsLemma54Label (z := z) σ τG (μ * x * μ⁻¹) e)
    (hlab : IsLemma54Label (z := z) σ τG a e) :
    ∃ y ∈ H z ⊓ centralizer ({a} : Set G), y ∉ centralizer ({z₁} : Set G) := by
  have hμa := hμe a hlab
  obtain ⟨q₂, hq₂, hμaeq⟩ := hμa
  obtain ⟨q₁, hq₁, haeq⟩ := hlab
  let y := q₁ * q₂⁻¹ * μ
  refine ⟨y, Subgroup.mem_inf.mpr ⟨lemma54_y_mem_H C hq₁ hq₂,
    lemma54_y_centralizes C he hq₁ hq₂ haeq hμaeq⟩, ?_⟩
  exact lemma54_y_not_centralizer C hq₁ hq₂

private theorem lemma54_hO56 [DecidableEq G] {z z₁ σ τG ℓ₀ lam μ : G}
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ) :
    ∀ a, a ∈ lemma54OrbitFamily z σ τG z₁ lam 5 ∨
      a ∈ lemma54OrbitFamily z σ τG z₁ lam 6 →
      ∃ y ∈ H z ⊓ centralizer ({a} : Set G), y ∉ centralizer ({z₁} : Set G) := by
  intro a ha
  rcases ha with ha5 | ha6
  · change a ∈ lemma54OuterF z σ τG (lam * z₁) at ha5
    exact lemma54_hO56_aux C (lemma54_lamz₁_mem C)
      (fun x hx => (lemma54_hswap C (C.basic.hμN) (C.basic.hμz₁)).2.2.1 x hx)
      (mem_lemma54OuterF.mp ha5)
  · change a ∈ lemma54OuterF z σ τG (lam * z₁ * z) at ha6
    exact lemma54_hO56_aux C (lemma54_lamz₁z_mem C)
      (fun x hx => (lemma54_hswap C (C.basic.hμN) (C.basic.hμz₁)).2.2.2 x hx)
      (mem_lemma54OuterF.mp ha6)

private theorem lemma54_hT1O [DecidableEq G]
    (h : Tim79a.ParrottHyp z) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    {S₀ : Subgroup G} (hS₀H : S₀ ≤ H z) (hτz₁ : (τ : G) * z₁ ∈ centerIn S₀)
    (hZS₀ : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = (τ : G) * z₁ ∨ e = (τ : G) * z₁ * z)
    (hy : ∃ y ∈ S₀, y ∉ centralizer ({z₁} : Set G))
    {σ τG ℓ₀ lam μ : G} (hτG : τG = (τ : G))
    (C : Lemma54Context z z₁ σ τG ℓ₀ lam μ)
    (hOW : ∀ i, ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i,
      a ∈ lemma54W z σ τG ∧ a ≠ 1)
    (hcover : ∀ a ∈ lemma54W z σ τG, a ≠ 1 →
      ∃ i, a ∈ lemma54OrbitFamily z σ τG z₁ lam i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (lemma54OrbitFamily z σ τG z₁ lam i)
      (lemma54OrbitFamily z σ τG z₁ lam j))
    (hcard : ∀ i, (lemma54OrbitFamily z σ τG z₁ lam i).card = lemma54Sizes i)
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam i, a ∉ J z)
    (hO56 : ∀ a, a ∈ lemma54OrbitFamily z σ τG z₁ lam 5 ∨
      a ∈ lemma54OrbitFamily z σ τG z₁ lam 6 →
      ∃ y ∈ H z ⊓ centralizer ({a} : Set G), y ∉ centralizer ({z₁} : Set G)) :
    (∃ u ∈ H z, ∃ a ∈ lemma54OrbitFamily z σ τG z₁ lam 5,
        u * a * u⁻¹ ∈ lemma54OrbitFamily z σ τG z₁ lam 6) ∨
      ((∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨
          e ∈ lemma54OrbitFamily z σ τG z₁ lam 5 ∨
          e ∈ lemma54OrbitFamily z σ τG z₁ lam 6) ∧
        τG ∈ lemma54OrbitFamily z σ τG z₁ lam 4 ∧
        τG * z ∈ lemma54OrbitFamily z σ τG z₁ lam 4) := by
  have hO5z : ∀ a ∈ lemma54OrbitFamily z σ τG z₁ lam 5,
      a * z ∈ lemma54OrbitFamily z σ τG z₁ lam 6 := by
    intro a ha
    change a ∈ lemma54OuterF z σ τG (lam * z₁) at ha
    change a * z ∈ lemma54OuterF z σ τG (lam * z₁ * z)
    obtain ⟨q, hq, rfl⟩ := mem_lemma54OuterF.mp ha
    exact mem_lemma54OuterF.mpr ⟨q, hq, by group⟩
  have hz₁W : z₁ ∈ lemma54W z σ τG :=
    Subgroup.mem_sup_left (C.blackA.hcenter_le C.blackA.hz₁)
  have hτW : τG ∈ lemma54W z σ τG :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers τG)
  have hZS : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = τG * z₁ ∨ e = τG * z₁ * z := by
    simpa only [hτG] using hZS₀
  have hτz₁' : τG * z₁ ∈ centerIn S₀ := by simpa only [hτG] using hτz₁
  obtain ⟨y, hyS, hyz₁⟩ := hy
  have hyH : y ∈ H z := hS₀H hyS
  exact exists_conj_mem_O6_or_mem_O4 (z := z) h (lemma54OrbitFamily z σ τG z₁ lam)
    hz₁ hz₁z hord (W := lemma54W z σ τG) (S₀ := S₀) hOW hcover hdisj hcard hJ hnJ
    hO56 hO5z hz₁W hτW C.basic.hτJ hZS hτz₁' hyH hyS hyz₁

private lemma lemma54_setup_data [DecidableEq G]
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∃ (ℓ₀ lam μ : G),
      ∃ C : Lemma54Context z z₁ ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
        ℓ₀ lam μ, True := by
  obtain ⟨ℓ₀, lam, hℓ₀, hlam, hlabel, hkey⟩ :=
    lemma54_outer_label_data (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) rfl rfl
  obtain ⟨μ, hμN, hμz₁, hμH, hμz, hμz₁'⟩ :=
    lemma54_mu_data (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) rfl rfl
  let C : Lemma54Context z z₁ ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
      ℓ₀ lam μ :=
    lemma54_context (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ℓ₀ lam μ rfl rfl
      hℓ₀ hlam hlabel hkey hμN hμz₁ hμH hμz hμz₁'
  exact ⟨ℓ₀, lam, μ, C, trivial⟩

theorem exists_lemma54_orbits [DecidableEq G]
    (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {S₀ : Subgroup G} (hS₀H : S₀ ≤ H z) (hτz₁ : (τ : G) * z₁ ∈ centerIn S₀)
    (hZS₀ : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = (τ : G) * z₁ ∨ e = (τ : G) * z₁ * z)
    (hy : ∃ y ∈ S₀, y ∉ centralizer ({z₁} : Set G)) :
    ∃ O : Fin 7 → Finset G,
      (∀ i, ∀ a ∈ O i,
        a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ∧ a ≠ 1) ∧
      (∀ a ∈ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G), a ≠ 1 →
        ∃ i, a ∈ O i) ∧
      (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧
      (∀ i, ∀ a ∈ O i, ∀ b ∈ O i,
        ∃ c ∈ normalizer
            (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) : Set G) ⊓
          centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓ H z,
          c * a * c⁻¹ = b) ∧
      (∀ i, ∀ a ∈ O i,
        ∀ c ∈ normalizer
            (lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) : Set G) ⊓
          centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓ H z,
          c * a * c⁻¹ ∈ O i) ∧
      (∀ i, (O i).card = lemma54Sizes i) ∧
      O 0 = {z} ∧ O 1 = {z₁, z₁ * z} ∧
      (∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z) ∧
      (∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z) ∧
      (∀ a ∈ O 2, a * z ∈ O 2) ∧ (∀ a ∈ O 3, a * z ∈ O 3) ∧
      J z ⊓ lemma54W z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) ≤
        Subgroup.closure ((O 2 : Set G) ∪ (O 3 : Set G)) ∧
      (∀ a, a ∈ O 5 ∨ a ∈ O 6 →
        ∃ y ∈ H z ⊓ centralizer ({a} : Set G), y ∉ centralizer ({z₁} : Set G)) ∧
      ((∃ u ∈ H z, ∃ a ∈ O 5, u * a * u⁻¹ ∈ O 6) ∨
        ((∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e ∈ O 5 ∨ e ∈ O 6) ∧
          (τ : G) ∈ O 4 ∧ (τ : G) * z ∈ O 4)) := by
  obtain ⟨ℓ₀, lam, μ, C, -⟩ :=
    lemma54_setup_data (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  exact ⟨lemma54OrbitFamily z ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) z₁ lam,
    lemma54_hOW C, lemma54_hcover C, lemma54_hdisj C, lemma54_horb C, lemma54_hinv C,
    lemma54_hcard C, lemma54_hO0 C, lemma54_hO1 C, lemma54_hJ C, lemma54_hnJ C,
    lemma54_hO2z C, lemma54_hO3z C, lemma54_hgen C, lemma54_hO56 C,
    lemma54_hT1O (D := D) h hz₁ hz₁z hord hqτ hS₀H hτz₁ hZS₀ hy rfl C
      (lemma54_hOW C) (lemma54_hcover C) (lemma54_hdisj C) (lemma54_hcard C)
      (lemma54_hJ C) (lemma54_hnJ C) (lemma54_hO56 C)⟩

end CFSG.RankThree.GF2n.Parrott
