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
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private noncomputable def l54S (D : QuotientData (z := z) hN) (σ₂ : ↥(H z)) : G :=
  ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)

private noncomputable def l54N (D : QuotientData (z := z) hN) (σ₂ τ : ↥(H z)) :
    Subgroup G :=
  lemma54N₀ (z := z) (l54S D σ₂) (τ : G)

private noncomputable def l54W (D : QuotientData (z := z) hN) (σ₂ τ : ↥(H z)) :
    Subgroup G :=
  lemma54W z (l54S D σ₂) (τ : G)

private noncomputable def l54Q (D : QuotientData (z := z) hN) (σ₂ : ↥(H z)) :
    Subgroup G :=
  J z ⊓ centralizer ({l54S D σ₂} : Set G)

private noncomputable def l54P (D : QuotientData (z := z) hN) (σ₂ τ : ↥(H z)) (z₁ : G) :
    Subgroup G :=
  l54N D σ₂ τ ⊓ centralizer ({z₁} : Set G)

private theorem l54_tau_sq {τ : ↥(H z)} (hτ : τ * τ = 1) :
    (τ : G) * (τ : G) = 1 := by
  simpa using congrArg Subtype.val hτ

private theorem l54_tau_notMem_J {D : QuotientData (z := z) hN} {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) :
    (τ : G) ∉ J z := by
  intro hmem
  have hq : qH (z := z) D τ = 1 :=
    (J_mem_iff (z := z) D τ).mp (Subgroup.mem_subgroupOf.mpr hmem)
  rw [hqτ] at hq
  exact t_ne_one (congrArg Subtype.val hq)

private theorem l54_tau_ne_one {D : QuotientData (z := z) hN} {τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) :
    (τ : G) ≠ 1 :=
  fun h1 => l54_tau_notMem_J hqτ (h1 ▸ Subgroup.one_mem (J z))

private theorem l54_tau_ord {D : QuotientData (z := z) hN} {τ : ↥(H z)}
    (hτ : τ * τ = 1) (hqτ : qH (z := z) D τ = tA) : orderOf (τ : G) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact l54_tau_sq hτ) (l54_tau_ne_one hqτ)

private theorem l54_tau_mem_W (D : QuotientData (z := z) hN) {σ₂ τ : ↥(H z)} :
    (τ : G) ∈ l54W D σ₂ τ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers (τ : G))

private theorem l54_mem_H_of_mem_N {D : QuotientData (z := z) hN} {σ₂ τ : ↥(H z)} {g : G}
    (hg : g ∈ l54N D σ₂ τ) : g ∈ H z :=
  (Subgroup.mem_inf.mp hg).2

private theorem l54_mem_centralizer_sigma_of_mem_N {D : QuotientData (z := z) hN}
    {σ₂ τ : ↥(H z)} {g : G} (hg : g ∈ l54N D σ₂ τ) :
    g ∈ centralizer ({l54S D σ₂} : Set G) :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2

private theorem l54_mem_normalizer_of_mem_N {D : QuotientData (z := z) hN}
    {σ₂ τ : ↥(H z)} {g : G} (hg : g ∈ l54N D σ₂ τ) :
    g ∈ Subgroup.normalizer (l54W D σ₂ τ : Set G) :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1

private theorem l54_conj_tau_mem_W {D : QuotientData (z := z) hN} {σ₂ τ : ↥(H z)} {g : G}
    (hg : g ∈ l54N D σ₂ τ) : g * (τ : G) * g⁻¹ ∈ l54W D σ₂ τ :=
  (Subgroup.mem_normalizer_iff.mp (l54_mem_normalizer_of_mem_N hg) (τ : G)).mp
    (l54_tau_mem_W D)

private theorem l54_conj_tau_notMem_J {D : QuotientData (z := z) hN} {σ₂ τ : ↥(H z)}
    (hqτ : qH (z := z) D τ = tA) {g : G} (hg : g ∈ l54N D σ₂ τ) :
    g * (τ : G) * g⁻¹ ∉ J z := by
  intro hconj
  have hgH : g ∈ H z := l54_mem_H_of_mem_N hg
  have hinv : g⁻¹ ∈ H z := (H z).inv_mem hgH
  have h2 : g⁻¹ * (g * (τ : G) * g⁻¹) * (g⁻¹)⁻¹ ∈ J z :=
    conj_mem_J_of_mem_H hinv hconj
  have hτ : (τ : G) ∈ J z := by
    rwa [show g⁻¹ * (g * (τ : G) * g⁻¹) * (g⁻¹)⁻¹ = (τ : G) by group] at h2
  exact l54_tau_notMem_J hqτ hτ

private noncomputable def l54Label (D : QuotientData (z := z) hN) (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    (g : G) : ↥(centerIn (J z)) := by
  classical
  exact if hex : ∃ e ∈ centerIn (J z),
      IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (g * (τ : G) * g⁻¹) e
    then ⟨hex.choose, hex.choose_spec.1⟩
    else 1

private theorem l54_label_self (D : QuotientData (z := z) hN) {σ₂ τ : ↥(H z)} :
    IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (τ : G) 1 := by
  refine ⟨1, Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, ?_⟩, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp

private theorem l54Label_spec (D : QuotientData (z := z) hN) (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {g : G} (hg : g ∈ l54N D σ₂ τ) :
    IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (g * (τ : G) * g⁻¹)
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) := by
  have hex : ∃ e ∈ centerIn (J z),
      IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (g * (τ : G) * g⁻¹) e :=
    exists_isLemma54Label (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (l54_conj_tau_mem_W hg) (l54_conj_tau_notMem_J hqτ hg)
  have hval : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) = hex.choose := by
    simp only [l54Label, dif_pos hex]
  rw [hval]
  exact hex.choose_spec.2

private theorem l54_label_mul (D : QuotientData (z := z) hN) (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {g h' : G} (hg : g ∈ l54N D σ₂ τ) (hh : h' ∈ l54N D σ₂ τ)
    (hgc : g ∈ centralizer (centerIn (J z) : Set G)) :
    l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (g * h') =
      l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g *
        l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' := by
  apply Subtype.ext
  have hspec := l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (Subgroup.mul_mem (l54N D σ₂ τ) hg hh)
  have hR := isLemma54Label_conj (z := z) (σ := l54S D σ₂) (τ := (τ : G)) (g := g)
    (x := h' * (τ : G) * h'⁻¹)
    (e := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G))
    (ℓ := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G))
    (l54_mem_H_of_mem_N hg) (l54_mem_centralizer_sigma_of_mem_N hg)
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g).2
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hg)
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hh)
  have hℓg : g * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G) * g⁻¹ =
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G) := by
    have hc := Subgroup.mem_centralizer_iff.mp hgc
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h')
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h').2
    calc g * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G) * g⁻¹
        = ((l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G) * g) * g⁻¹ := by
          rw [← hc]
      _ = (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G) := by group
  have hx : (g * h') * (τ : G) * (g * h')⁻¹ = g * (h' * (τ : G) * h'⁻¹) * g⁻¹ := by
    group
  have hR' : IsLemma54Label (z := z) (l54S D σ₂) (τ : G)
      (g * (h' * (τ : G) * h'⁻¹) * g⁻¹)
      ((l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) *
        (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h' : G)) := by
    simpa [hℓg] using hR
  exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (g * h')).2
    (Subgroup.mul_mem (centerIn (J z)) (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g).2
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ h').2)
    (by rw [← hx]; exact hspec) hR'

private theorem l54_mem_centralizer_centerIn_of_mem_P (h : Tim79a.ParrottHyp z)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2) {D : QuotientData (z := z) hN} {σ₂ τ : ↥(H z)} {g : G}
    (hg : g ∈ l54P D σ₂ τ z₁) : g ∈ centralizer (centerIn (J z) : Set G) := by
  obtain ⟨hgN, hgz₁⟩ := Subgroup.mem_inf.mp hg
  have hgH : g ∈ H z := l54_mem_H_of_mem_N hgN
  have hzg : z * g = g * z := (Subgroup.mem_centralizer_singleton_iff.mp hgH).symm
  have hz₁g : z₁ * g = g * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp hgz₁).symm
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp he with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hzg
  · exact hz₁g
  · calc z * z₁ * g = z * (z₁ * g) := by group
      _ = z * (g * z₁) := by rw [hz₁g]
      _ = (z * g) * z₁ := by group
      _ = (g * z) * z₁ := by rw [hzg]
      _ = g * (z * z₁) := by group

private theorem l54_mem_centralizer_z1_of_mem_J {z₁ q : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hq : q ∈ J z) : q ∈ centralizer ({z₁} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hz₁.2 q hq

private theorem l54_tau_mem_centralizer_z1 {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) :
    (τ : G) ∈ centralizer ({z₁} : Set G) := by
  have hmem : z₁ ∈ J z ⊓ centralizer ({l54S D σ₂} : Set G) ⊓
      centralizer ({(τ : G)} : Set G) :=
    centerIn_J_le_lemma54N (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hz₁
  have hτ : z₁ * (τ : G) = (τ : G) * z₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hmem).2
  exact Subgroup.mem_centralizer_singleton_iff.mpr hτ.symm

private theorem l54_tau_mem_centralizer_sigma {D : QuotientData (z := z) hN}
    {σ₂ τ : ↥(H z)} (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (τ : G) ∈ centralizer ({l54S D σ₂} : Set G) := by
  have h2 : τ * σ₂⁻¹ = σ₂⁻¹ * τ := (show Commute τ σ₂ from hτ₂).inv_right.eq
  have hcomm : τ * (sigma1Nine (z := z) D * σ₂⁻¹) =
      (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by
    calc τ * (sigma1Nine (z := z) D * σ₂⁻¹) =
        (τ * sigma1Nine (z := z) D) * σ₂⁻¹ := by group
      _ = (sigma1Nine (z := z) D * τ) * σ₂⁻¹ := by rw [hτ₁]
      _ = sigma1Nine (z := z) D * (τ * σ₂⁻¹) := by group
      _ = sigma1Nine (z := z) D * (σ₂⁻¹ * τ) := by rw [h2]
      _ = (sigma1Nine (z := z) D * σ₂⁻¹) * τ := by group
  exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)

private theorem l54_conj_tau_mem_Q {D : QuotientData (z := z) hN} {σ₂ τ : ↥(H z)}
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {q : G} (hq : q ∈ l54Q D σ₂) :
    (τ : G) * q * (τ : G)⁻¹ ∈ l54Q D σ₂ := by
  obtain ⟨hqJ, hqS⟩ := Subgroup.mem_inf.mp hq
  refine Subgroup.mem_inf.mpr ⟨conj_mem_J_of_mem_H τ.2 hqJ, ?_⟩
  have hτS : (τ : G) * l54S D σ₂ = l54S D σ₂ * (τ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (l54_tau_mem_centralizer_sigma hτ₁ hτ₂)
  have hinvS : (τ : G)⁻¹ * l54S D σ₂ = l54S D σ₂ * (τ : G)⁻¹ :=
    (show Commute (τ : G) (l54S D σ₂) from hτS).inv_left.eq
  rw [Subgroup.mem_centralizer_singleton_iff] at hqS ⊢
  calc (τ : G) * q * (τ : G)⁻¹ * l54S D σ₂
      = (τ : G) * q * ((τ : G)⁻¹ * l54S D σ₂) := by group
    _ = (τ : G) * q * (l54S D σ₂ * (τ : G)⁻¹) := by rw [hinvS]
    _ = (τ : G) * (q * l54S D σ₂) * (τ : G)⁻¹ := by group
    _ = (τ : G) * (l54S D σ₂ * q) * (τ : G)⁻¹ := by rw [hqS]
    _ = ((τ : G) * l54S D σ₂) * q * (τ : G)⁻¹ := by group
    _ = (l54S D σ₂ * (τ : G)) * q * (τ : G)⁻¹ := by rw [hτS]
    _ = l54S D σ₂ * ((τ : G) * q * (τ : G)⁻¹) := by group

private theorem l54_tau_mem_normalizer_Q {D : QuotientData (z := z) hN} {σ₂ τ : ↥(H z)}
    (hτ : τ * τ = 1) (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ)
    (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (τ : G) ∈ Subgroup.normalizer (l54Q D σ₂ : Set G) := by
  have hτG : (τ : G) * (τ : G) = 1 := l54_tau_sq hτ
  have hinv : (τ : G)⁻¹ = (τ : G) := inv_eq_of_mul_eq_one_right hτG
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    exact l54_conj_tau_mem_Q hτ₁ hτ₂ hq
  · intro hq
    have h2 := l54_conj_tau_mem_Q hτ₁ hτ₂ hq
    have hsimp : (τ : G) * ((τ : G) * q * (τ : G)⁻¹) * (τ : G)⁻¹ = q := by
      rw [hinv]
      calc (τ : G) * ((τ : G) * q * (τ : G)) * (τ : G)
          = ((τ : G) * (τ : G)) * q * ((τ : G) * (τ : G)) := by group
        _ = 1 * q * 1 := by rw [hτG]
        _ = q := by rw [one_mul, mul_one]
    rwa [hsimp] at h2

private theorem l54_label_eq_one_of_mem_Q {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {q : G} (hq : q ∈ l54Q D σ₂) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ q : G) = 1 := by
  have hqN : q ∈ l54N D σ₂ τ :=
    mem_lemma54N₀_of_mem_J (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq
  have hbase : IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (q * (τ : G) * q⁻¹) 1 :=
    ⟨q, hq, by rw [mul_one]⟩
  exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ q).2 (Subgroup.one_mem (centerIn (J z)))
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hqN) hbase

private theorem l54_label_eq_one_of_mem_zpowers_tau {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {x : G} (hx : x ∈ Subgroup.zpowers (τ : G)) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ x : G) = 1 := by
  have hxN : x ∈ l54N D σ₂ τ :=
    Subgroup.zpowers_le.mpr
      (tau_mem_lemma54N₀ (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂) hx
  have hxτ : x * (τ : G) * x⁻¹ = (τ : G) := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : (τ : G) ^ k * (τ : G) = (τ : G) * (τ : G) ^ k :=
      ((Commute.refl (τ : G)).zpow_left k).eq
    rw [hcomm, mul_inv_cancel_right]
  have hbase : IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (x * (τ : G) * x⁻¹) 1 := by
    rw [hxτ]
    exact l54_label_self D
  exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ x).2 (Subgroup.one_mem (centerIn (J z)))
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hxN) hbase

private theorem l54_card_sup_Q_tau
    {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    Nat.card ↥(l54Q D σ₂ ⊔ Subgroup.zpowers (τ : G)) = 2 ^ 7 := by
  have hQ : Nat.card ↥(l54Q D σ₂) = 2 ^ 6 :=
    card_J_inf_centralizer_sigma1Nine_mul_inv_of_spin (z := z) D h P hP hσ₂ hq₂ hc₂
  have hτc : Nat.card ↥(Subgroup.zpowers (τ : G)) = 2 := by
    rw [Nat.card_zpowers]
    exact l54_tau_ord hτ hqτ
  have hdisj : Disjoint (l54Q D σ₂) (Subgroup.zpowers (τ : G)) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hxQ, hxτ⟩ := Subgroup.mem_inf.mp hx
    have hxJ : x ∈ J z := (Subgroup.mem_inf.mp hxQ).1
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two (l54_tau_ord hτ hqτ) hxτ
      with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxJ (l54_tau_notMem_J hqτ)
  have hnorm : Subgroup.zpowers (τ : G) ≤ Subgroup.normalizer (l54Q D σ₂ : Set G) :=
    Subgroup.zpowers_le.mpr (l54_tau_mem_normalizer_Q hτ hτ₁ hτ₂)
  rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj, hQ, hτc]
  norm_num

private theorem l54_card_Y_inf_A {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    Nat.card ↥((H z ⊓ centralizer ({l54S D σ₂} : Set G)) ⊓
      (H z ⊓ centralizer ({z₁} : Set G))) = 2 ^ 7 * 27 := by
  let Y : Subgroup G := H z ⊓ centralizer ({l54S D σ₂} : Set G)
  let A : Subgroup G := H z ⊓ centralizer ({z₁} : Set G)
  show Nat.card ↥(Y ⊓ A) = 2 ^ 7 * 27
  have hYcard : Nat.card ↥Y = 6912 :=
    card_lemma54Y (z := z) D h P hP hσ₂ hq₂ hc₂
  have hrel_le : (Y ⊓ A).relIndex Y ≤ 2 := by
    have h1 : (Y ⊓ A).relIndex Y = A.relIndex Y := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    have h2 : A.relIndex Y ≤ A.relIndex (H z) :=
      Subgroup.relIndex_le_of_le_right (H := A) (K := Y) (L := H z) inf_le_left
        (by rw [relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hord]; norm_num)
    rwa [relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hord] at h2
  have hrel_ne_one : (Y ⊓ A).relIndex Y ≠ 1 := by
    intro h1
    have hle : Y ≤ Y ⊓ A := Subgroup.relIndex_eq_one.mp h1
    obtain ⟨μ, hμN, hμc⟩ :=
      exists_mem_lemma54N₀_not_mem_centralizer_z1 (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂
        hc₂ hqτ hτ hτ₁ hτ₂
    have hμY : μ ∈ Y :=
      Subgroup.mem_inf.mpr ⟨l54_mem_H_of_mem_N hμN, l54_mem_centralizer_sigma_of_mem_N hμN⟩
    exact hμc (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hle hμY)).2).2
  have hrel_ne_zero : (Y ⊓ A).relIndex Y ≠ 0 := by
    intro h0
    have hmul := Subgroup.relIndex_mul_card (Y ⊓ A) Y
    rw [h0, zero_mul, hYcard] at hmul
    omega
  have hrel : (Y ⊓ A).relIndex Y = 2 := by omega
  have hmul := Subgroup.relIndex_mul_card (Y ⊓ A) Y
  rw [hrel, hYcard, show (Y ⊓ A) ⊓ Y = Y ⊓ A from inf_eq_left.mpr inf_le_left] at hmul
  have h3456 : Nat.card ↥(Y ⊓ A) = 3456 := by omega
  rw [h3456]
  norm_num

private theorem l54_card_P_dvd {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    Nat.card ↥(l54P D σ₂ τ z₁) ∣ 2 ^ 7 * 27 := by
  have hPle : l54P D σ₂ τ z₁ ≤ (H z ⊓ centralizer ({l54S D σ₂} : Set G)) ⊓
      (H z ⊓ centralizer ({z₁} : Set G)) := by
    intro x hx
    obtain ⟨hxN, hxz₁⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨l54_mem_H_of_mem_N hxN, l54_mem_centralizer_sigma_of_mem_N hxN⟩,
        Subgroup.mem_inf.mpr ⟨l54_mem_H_of_mem_N hxN, hxz₁⟩⟩
  have hdvd := Subgroup.card_dvd_of_le hPle
  rwa [l54_card_Y_inf_A h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂] at hdvd
private noncomputable def l54Hom {D : QuotientData (z := z) hN} (h : Tim79a.ParrottHyp z)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ↥(l54P D σ₂ τ z₁) →* ↥(centerIn (J z)) where
  toFun g := l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (g : G)
  map_one' := by
    apply Subtype.ext
    show (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      ((1 : ↥(l54P D σ₂ τ z₁)) : G) : G) = 1
    rw [Subgroup.coe_one]
    have hx : (1 : G) * (τ : G) * (1 : G)⁻¹ = (τ : G) := by group
    have hspec : IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (1 * (τ : G) * 1⁻¹)
        (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ 1) :=
      l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
        (Subgroup.one_mem (l54N D σ₂ τ))
    rw [hx] at hspec
    exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ 1).2 (Subgroup.one_mem (centerIn (J z)))
      hspec (l54_label_self D)
  map_mul' p q := by
    apply Subtype.ext
    have hgc := l54_mem_centralizer_centerIn_of_mem_P h hz₁ hz₁z hord p.2
    have hmul := l54_label_mul D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (Subgroup.mem_inf.mp p.2).1 (Subgroup.mem_inf.mp q.2).1 hgc
    simpa using congrArg Subtype.val hmul

private theorem l54_two_pow_seven_dvd_ker
    {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    2 ^ 7 ∣ Nat.card ↥(l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂).ker := by
  let F := l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  let K : Subgroup G := F.ker.map (l54P D σ₂ τ z₁).subtype
  have hQle : l54Q D σ₂ ≤ K := by
    intro q hq
    have hqN : q ∈ l54N D σ₂ τ :=
      mem_lemma54N₀_of_mem_J (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq
    have hqz : q ∈ centralizer ({z₁} : Set G) :=
      l54_mem_centralizer_z1_of_mem_J hz₁ (Subgroup.mem_inf.mp hq).1
    have hqP : q ∈ l54P D σ₂ τ z₁ := Subgroup.mem_inf.mpr ⟨hqN, hqz⟩
    have hqk : (⟨q, hqP⟩ : ↥(l54P D σ₂ τ z₁)) ∈ F.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact l54_label_eq_one_of_mem_Q h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hq
    exact Subgroup.mem_map.mpr ⟨⟨q, hqP⟩, hqk, rfl⟩
  have hτle : Subgroup.zpowers (τ : G) ≤ K := by
    have hτP : (τ : G) ∈ l54P D σ₂ τ z₁ :=
      Subgroup.mem_inf.mpr
        ⟨tau_mem_lemma54N₀ (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂,
          l54_tau_mem_centralizer_z1 h P hP hσ₂ hq₂ hc₂ hqτ hτ₁ hτ₂ hz₁⟩
    have hτk : (⟨(τ : G), hτP⟩ : ↥(l54P D σ₂ τ z₁)) ∈ F.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact l54_label_eq_one_of_mem_zpowers_tau h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
        (Subgroup.mem_zpowers (τ : G))
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr ⟨⟨(τ : G), hτP⟩, hτk, rfl⟩)
  have hsup : l54Q D σ₂ ⊔ Subgroup.zpowers (τ : G) ≤ K := sup_le hQle hτle
  have hdvd : Nat.card ↥(l54Q D σ₂ ⊔ Subgroup.zpowers (τ : G)) ∣ Nat.card ↥K :=
    Subgroup.card_dvd_of_le hsup
  rw [l54_card_sup_Q_tau h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂] at hdvd
  have hcardK : Nat.card ↥K = Nat.card ↥F.ker :=
    Subgroup.card_map_of_injective (l54P D σ₂ τ z₁).subtype_injective
  rwa [hcardK] at hdvd

private theorem l54_ker_index_dvd_four {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hord : orderOf z₁ = 2)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂).ker.index ∣ 4 := by
  let F := l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  show F.ker.index ∣ 4
  rw [Subgroup.index_ker]
  have hdvd : Nat.card ↥F.range ∣ Nat.card ↥(⊤ : Subgroup ↥(centerIn (J z))) :=
    Subgroup.card_dvd_of_le (le_top : F.range ≤ ⊤)
  rw [Subgroup.card_top] at hdvd
  rwa [card_centerIn_J h] at hdvd

private theorem l54_ker_index_dvd_27 {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    (l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂).ker.index ∣ 27 := by
  let F := l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  show F.ker.index ∣ 27
  have hik : F.ker.index * Nat.card ↥F.ker = Nat.card ↥(l54P D σ₂ τ z₁) :=
    Subgroup.index_mul_card _
  have h2k : 2 ^ 7 ∣ Nat.card ↥F.ker :=
    l54_two_pow_seven_dvd_ker h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  have hp : Nat.card ↥(l54P D σ₂ τ z₁) ∣ 2 ^ 7 * 27 :=
    l54_card_P_dvd h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  have h2 : 2 ^ 7 * (F.ker.index * (Nat.card ↥F.ker / 2 ^ 7)) ∣ 2 ^ 7 * 27 := by
    have hk' : 2 ^ 7 * (Nat.card ↥F.ker / 2 ^ 7) = Nat.card ↥F.ker := by
      rw [mul_comm]
      exact Nat.div_mul_cancel h2k
    have hEq : 2 ^ 7 * (F.ker.index * (Nat.card ↥F.ker / 2 ^ 7)) =
        Nat.card ↥(l54P D σ₂ τ z₁) := by
      calc 2 ^ 7 * (F.ker.index * (Nat.card ↥F.ker / 2 ^ 7))
          = F.ker.index * (2 ^ 7 * (Nat.card ↥F.ker / 2 ^ 7)) := by ring
        _ = F.ker.index * Nat.card ↥F.ker := by rw [hk']
        _ = Nat.card ↥(l54P D σ₂ τ z₁) := hik
    rw [hEq]
    exact hp
  have h3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2 ^ 7) h2
  exact dvd_trans (Nat.dvd_mul_right _ _) h3

private theorem l54_label_eq_one_of_mem_P
    {D : QuotientData (z := z) hN}
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {g : G} (hg : g ∈ l54P D σ₂ τ z₁) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) = 1 := by
  let F := l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
  have hidx : F.ker.index ∣ 1 := by
    have h4 : (l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂).ker.index ∣ 4 :=
      l54_ker_index_dvd_four h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    have h27 : (l54Hom h P hP hz₁ hz₁z hord hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂).ker.index ∣ 27 :=
      l54_ker_index_dvd_27 h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    have h := Nat.dvd_gcd h4 h27
    rw [show Nat.gcd 4 27 = 1 from by norm_num] at h
    simpa using h
  have htop : F.ker = ⊤ := Subgroup.index_eq_one.mp (Nat.dvd_one.mp hidx)
  have hmem : (⟨g, hg⟩ : ↥(l54P D σ₂ τ z₁)) ∈ F.ker := by
    rw [htop]
    exact Subgroup.mem_top _
  have hone : F ⟨g, hg⟩ = 1 := MonoidHom.mem_ker.mp hmem
  exact congrArg Subtype.val hone

theorem isLemma54Label_conj_tau_of_mem_centralizer_z1
    (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {g : G} (hg : g ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G))
    (hgz₁ : g ∈ centralizer ({z₁} : Set G)) :
    IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
      (g * τ * g⁻¹) 1 := by
  have hgP : g ∈ l54P D σ₂ τ z₁ := Subgroup.mem_inf.mpr ⟨hg, hgz₁⟩
  have h1 : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) = 1 :=
    l54_label_eq_one_of_mem_P h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hgP
  have hspec := l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hg
  rwa [h1] at hspec

private theorem l54_conj_inv_z₁_eq (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {μ : G} (hμH : μ ∈ H z) (hμc : μ ∉ centralizer ({z₁} : Set G)) :
    μ⁻¹ * z₁ * μ = z * z₁ := by
  have hμinvH : μ⁻¹ ∈ H z := (H z).inv_mem hμH
  have hμinvc : μ⁻¹ ∉ centralizer ({z₁} : Set G) := by
    intro h
    exact hμc (by simpa using (Subgroup.centralizer ({z₁} : Set G)).inv_mem h)
  have h := conj_z1_eq_of_not_mem_centralizer (h := h) hz₁ hz₁z hord hμinvH hμinvc
  simpa using h

private theorem l54_conj_inv_z_eq {μ : G} (hμH : μ ∈ H z) : μ⁻¹ * z * μ = z := by
  have hcomm : Commute μ z := Subgroup.mem_centralizer_singleton_iff.mp hμH
  rw [(hcomm.inv_left).eq, mul_assoc, inv_mul_cancel, mul_one]

private theorem l54_conj_mem_centerIn {e g : G} (he : e ∈ centerIn (J z)) (hg : g ∈ H z) :
    g * e * g⁻¹ ∈ centerIn (J z) := by
  have hHN : H z ≤ Subgroup.normalizer (centerIn (J z) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centerIn_le_H (z := z))).mp
      (centerIn_subgroupOf_normal z)
  exact (Subgroup.mem_normalizer_iff.mp (hHN hg) e).mp he

private theorem l54_inv_mul_mem_centralizer_z1 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {μ g : G} (hμH : μ ∈ H z) (hμc : μ ∉ centralizer ({z₁} : Set G))
    (hgH : g ∈ H z) (hgc : g ∉ centralizer ({z₁} : Set G)) :
    μ⁻¹ * g ∈ centralizer ({z₁} : Set G) := by
  have hgconj : g * z₁ * g⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hgH hgc
  have hμinvz₁ : μ⁻¹ * z₁ * μ = z * z₁ := l54_conj_inv_z₁_eq h hz₁ hz₁z hord hμH hμc
  have hμinvz : μ⁻¹ * z * μ = z := l54_conj_inv_z_eq hμH
  have zsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  have hconj : (μ⁻¹ * g) * z₁ * (μ⁻¹ * g)⁻¹ = z₁ := by
    calc (μ⁻¹ * g) * z₁ * (μ⁻¹ * g)⁻¹ = μ⁻¹ * (g * z₁ * g⁻¹) * μ := by group
      _ = μ⁻¹ * (z * z₁) * μ := by rw [hgconj]
      _ = (μ⁻¹ * z * μ) * (μ⁻¹ * z₁ * μ) := by group
      _ = z * (z * z₁) := by rw [hμinvz, hμinvz₁]
      _ = z₁ := by rw [← mul_assoc, zsq, one_mul]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc (μ⁻¹ * g) * z₁ = ((μ⁻¹ * g) * z₁ * (μ⁻¹ * g)⁻¹) * (μ⁻¹ * g) := by group
    _ = z₁ * (μ⁻¹ * g) := by rw [hconj]

private theorem l54_sq_mem_centralizer_z1 (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {μ : G} (hμH : μ ∈ H z) (hμc : μ ∉ centralizer ({z₁} : Set G)) :
    μ * μ ∈ centralizer ({z₁} : Set G) := by
  have hμz : μ * z * μ⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hμH, mul_inv_cancel_right]
  have hμz₁ : μ * z₁ * μ⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer (h := h) hz₁ hz₁z hord hμH hμc
  have zsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  have hconj : (μ * μ) * z₁ * (μ * μ)⁻¹ = z₁ := by
    calc (μ * μ) * z₁ * (μ * μ)⁻¹ = μ * (μ * z₁ * μ⁻¹) * μ⁻¹ := by group
      _ = μ * (z * z₁) * μ⁻¹ := by rw [hμz₁]
      _ = (μ * z * μ⁻¹) * (μ * z₁ * μ⁻¹) := by group
      _ = z * (z * z₁) := by rw [hμz, hμz₁]
      _ = z₁ := by rw [← mul_assoc, zsq, one_mul]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc μ * μ * z₁ = ((μ * μ) * z₁ * (μ * μ)⁻¹) * (μ * μ) := by group
    _ = z₁ * (μ * μ) := by rw [hconj]

private theorem l54_label_sq_eq_one
    {D : QuotientData (z := z) hN} (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {μ : G} (hμN : μ ∈ l54N D σ₂ τ) (hμc : μ ∉ centralizer ({z₁} : Set G)) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ * μ) : G) = 1 := by
  have hμ2N : μ * μ ∈ l54N D σ₂ τ := (l54N D σ₂ τ).mul_mem hμN hμN
  have hμ2C : μ * μ ∈ centralizer ({z₁} : Set G) :=
    l54_sq_mem_centralizer_z1 h hz₁ hz₁z hord (l54_mem_H_of_mem_N hμN) hμc
  refine isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ * μ)).2
    (Subgroup.one_mem (centerIn (J z))) (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμ2N) ?_
  exact isLemma54Label_conj_tau_of_mem_centralizer_z1 D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ
    hτ hτ₁ hτ₂ hμ2N hμ2C

private theorem l54_label_mu_mul_conj_eq_one
    {D : QuotientData (z := z) hN} (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {μ : G} (hμN : μ ∈ l54N D σ₂ τ) (hμc : μ ∉ centralizer ({z₁} : Set G)) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) *
      (μ * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) * μ⁻¹) = 1 := by
  have hμH : μ ∈ H z := l54_mem_H_of_mem_N hμN
  have hμ2N : μ * μ ∈ l54N D σ₂ τ := (l54N D σ₂ τ).mul_mem hμN hμN
  have hsq : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ * μ) : G) = 1 :=
    l54_label_sq_eq_one h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN hμc
  have hmul := isLemma54Label_conj (z := z) (σ := l54S D σ₂) (τ := (τ : G)) (g := μ)
    (x := μ * (τ : G) * μ⁻¹)
    (e := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G))
    (ℓ := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G))
    hμH (l54_mem_centralizer_sigma_of_mem_N hμN)
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ).2
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN)
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN)
  have hx : μ * (μ * (τ : G) * μ⁻¹) * μ⁻¹ = (μ * μ) * (τ : G) * (μ * μ)⁻¹ := by group
  have hmul' : IsLemma54Label (z := z) (l54S D σ₂) (τ : G) ((μ * μ) * (τ : G) * (μ * μ)⁻¹)
      ((l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) *
        (μ * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) * μ⁻¹)) := by
    rw [← hx]
    exact hmul
  have hlabelEq : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ * μ) : G) =
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) *
        (μ * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) * μ⁻¹) :=
    isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ * μ)).2
      (Subgroup.mul_mem (centerIn (J z))
        (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ).2
        (l54_conj_mem_centerIn (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ).2 hμH))
      (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμ2N) hmul'
  exact hlabelEq.symm.trans hsq

private theorem l54_eq_one_of_z1_mul {z₁ μ : G} (hord : orderOf z₁ = 2)
    (hzz₁ : z * z₁ = z₁ * z) (hμz₁ : μ * z₁ * μ⁻¹ = z * z₁)
    (hone : z₁ * (μ * z₁ * μ⁻¹) = 1) : z = 1 := by
  have z₁sq : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at this
  have hcontra : z₁ * (z * z₁) = 1 := by rwa [hμz₁] at hone
  calc z = z * 1 := (mul_one z).symm
    _ = z * (z₁ * z₁) := by rw [z₁sq]
    _ = (z * z₁) * z₁ := by group
    _ = (z₁ * z) * z₁ := by rw [hzz₁]
    _ = z₁ * (z * z₁) := by group
    _ = 1 := hcontra

private theorem l54_eq_one_of_zz1_mul {z₁ μ : G} (hord : orderOf z₁ = 2)
    (hμzz₁ : μ * (z * z₁) * μ⁻¹ = z₁)
    (hone : (z * z₁) * (μ * (z * z₁) * μ⁻¹) = 1) : z = 1 := by
  have z₁sq : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at this
  have hcontra : (z * z₁) * z₁ = 1 := by rwa [hμzz₁] at hone
  calc z = z * 1 := (mul_one z).symm
    _ = z * (z₁ * z₁) := by rw [z₁sq]
    _ = (z * z₁) * z₁ := by group
    _ = 1 := hcontra

private theorem l54_outer_label_mem
    {D : QuotientData (z := z) hN} (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {μ : G} (hμN : μ ∈ l54N D σ₂ τ) (hμc : μ ∉ centralizer ({z₁} : Set G)) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) = 1 ∨
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) = z := by
  have hμH : μ ∈ H z := l54_mem_H_of_mem_N hμN
  have hone := l54_label_mu_mul_conj_eq_one h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ
    hτ₁ hτ₂ hμN hμc
  have zsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  have hzz₁ : z * z₁ = z₁ * z := Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h)
  have z_ne_one : z ≠ 1 := by
    intro h1
    have := h.1
    rw [h1, orderOf_one] at this
    norm_num at this
  have hμz : μ * z * μ⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hμH, mul_inv_cancel_right]
  have hμz₁ : μ * z₁ * μ⁻¹ = z * z₁ :=
    conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hμH hμc
  have hμzz₁ : μ * (z * z₁) * μ⁻¹ = z₁ := by
    calc μ * (z * z₁) * μ⁻¹ = (μ * z * μ⁻¹) * (μ * z₁ * μ⁻¹) := by group
      _ = z * (z * z₁) := by rw [hμz, hμz₁]
      _ = z₁ := by rw [← mul_assoc, zsq, one_mul]
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ).2 with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exfalso
    have h1' : z₁ * (μ * z₁ * μ⁻¹) = 1 := by rwa [h1] at hone
    exact z_ne_one (l54_eq_one_of_z1_mul hord hzz₁ hμz₁ h1')
  · exfalso
    have h1' : (z * z₁) * (μ * (z * z₁) * μ⁻¹) = 1 := by rwa [h1] at hone
    exact z_ne_one (l54_eq_one_of_zz1_mul hord hμzz₁ h1')

private theorem l54_label_inv_mul_eq_one
    {D : QuotientData (z := z) hN} (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {μ g : G} (hμN : μ ∈ l54N D σ₂ τ) (hμc : μ ∉ centralizer ({z₁} : Set G))
    (hgN : g ∈ l54N D σ₂ τ) (hgc : g ∉ centralizer ({z₁} : Set G)) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ⁻¹ * g) : G) = 1 := by
  have hμH : μ ∈ H z := l54_mem_H_of_mem_N hμN
  have hgH : g ∈ H z := l54_mem_H_of_mem_N hgN
  have hpN : μ⁻¹ * g ∈ l54N D σ₂ τ :=
    (l54N D σ₂ τ).mul_mem ((l54N D σ₂ τ).inv_mem hμN) hgN
  have hpC : μ⁻¹ * g ∈ centralizer ({z₁} : Set G) :=
    l54_inv_mul_mem_centralizer_z1 h hz₁ hz₁z hord hμH hμc hgH hgc
  exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ⁻¹ * g)).2
    (Subgroup.one_mem (centerIn (J z)))
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hpN)
    (isLemma54Label_conj_tau_of_mem_centralizer_z1 D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
      hqτ hτ hτ₁ hτ₂ hpN hpC)

private theorem l54_label_eq_of_outer
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ)
    {μ g : G} (hμN : μ ∈ l54N D σ₂ τ) (hμc : μ ∉ centralizer ({z₁} : Set G))
    (hgN : g ∈ l54N D σ₂ τ) (hgc : g ∉ centralizer ({z₁} : Set G)) :
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) =
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) := by
  have hμH : μ ∈ H z := l54_mem_H_of_mem_N hμN
  have hgH : g ∈ H z := l54_mem_H_of_mem_N hgN
  have hpN : μ⁻¹ * g ∈ l54N D σ₂ τ :=
    (l54N D σ₂ τ).mul_mem ((l54N D σ₂ τ).inv_mem hμN) hgN
  have hpLab : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ⁻¹ * g) : G) = 1 :=
    l54_label_inv_mul_eq_one h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN hμc hgN hgc
  have hstep := isLemma54Label_conj (z := z) (σ := l54S D σ₂) (τ := (τ : G)) (g := μ)
    (x := (μ⁻¹ * g) * (τ : G) * (μ⁻¹ * g)⁻¹)
    (e := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ⁻¹ * g) : G))
    (ℓ := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G))
    hμH (l54_mem_centralizer_sigma_of_mem_N hμN)
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ).2
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN)
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hpN)
  have hxeq : μ * ((μ⁻¹ * g) * (τ : G) * (μ⁻¹ * g)⁻¹) * μ⁻¹ = g * (τ : G) * g⁻¹ := by
    group
  have hstep' : IsLemma54Label (z := z) (l54S D σ₂) (τ : G) (g * (τ : G) * g⁻¹)
      ((l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) *
        (μ * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ⁻¹ * g) : G) * μ⁻¹)) := by
    rw [← hxeq]
    exact hstep
  have hval : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) *
      (μ * (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ (μ⁻¹ * g) : G) * μ⁻¹) =
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) := by
    rw [hpLab]
    group
  rw [hval] at hstep'
  exact isLemma54Label_unique (z := z) D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g).2
    (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ).2
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hgN) hstep'

theorem exists_lemma54_outer_label (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {τ : ↥(H z)} (hqτ : qH (z := z) D τ = tA) (hτ : τ * τ = 1)
    (hτ₁ : τ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * τ) (hτ₂ : τ * σ₂ = σ₂ * τ) :
    ∃ ℓ₀ : G, (ℓ₀ = 1 ∨ ℓ₀ = z) ∧
      ∀ g ∈ lemma54N₀ (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G),
        g ∉ centralizer ({z₁} : Set G) → ∀ x e : G,
          IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G) x e →
          IsLemma54Label (z := z) ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) (τ : G)
            (g * x * g⁻¹) (ℓ₀ * (g * e * g⁻¹)) := by
  obtain ⟨μ, hμN, hμc⟩ :=
    exists_mem_lemma54N₀_not_mem_centralizer_z1 (z := z) D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
      hqτ hτ hτ₁ hτ₂
  refine ⟨(l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G),
    l54_outer_label_mem h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN hμc, ?_⟩
  intro g hgN hgc x e hx
  have hgH : g ∈ H z := l54_mem_H_of_mem_N hgN
  have hgσ : g ∈ centralizer ({l54S D σ₂} : Set G) :=
    l54_mem_centralizer_sigma_of_mem_N hgN
  have hlabg : (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G) =
      (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ μ : G) :=
    l54_label_eq_of_outer D h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hμN hμc hgN hgc
  have hres := isLemma54Label_conj (z := z) (σ := l54S D σ₂) (τ := (τ : G)) (g := g)
    (x := x) (e := e) (ℓ := (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g : G))
    hgH hgσ (l54Label D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ g).2
    (l54Label_spec D h P hP hσ₂ hq₂ hc₂ hqτ hτ hτ₁ hτ₂ hgN) hx
  rwa [hlabg] at hres

end CFSG.RankThree.GF2n.Parrott
