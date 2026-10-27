module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Conj
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Crit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

@[expose] def PushUp (A B : Subgroup D) : Prop :=
  ∀ x y : CosetGeom (A ⊔ B) A B, (graph (A ⊔ B) A B).Adj x y →
    ¬ stab x ≤ Subgroup.normalizer ((ballStab 1 x ⊓ ballStab 1 y : Subgroup D) : Set D)

theorem exists_nbr_not_le_of_not_normal (h : TwoSys A B z V c V₂)
    (h3 : GoldAmL3.GoldHyp3 A B z V) {α α' ε p₁ : CosetGeom (A ⊔ B) A B}
    (hαp : (graph (A ⊔ B) A B).Adj α p₁) (hα'ε : (graph (A ⊔ B) A B).Adj α' ε)
    (hαε : Nm A B V V₂ α ≤ ballStab 1 ε) (hα'p : Nm A B V V₂ α' ≤ ballStab 1 p₁)
    (hnot : ¬ Nm A B V V₂ α ≤ ballStab 1 α')
    (hPU : ¬ stab α' ≤ Subgroup.normalizer ((ballStab 1 α' ⊓ ballStab 1 ε : Subgroup D) : Set D)) :
    ∃ μ, (graph (A ⊔ B) A B).Adj α' μ ∧ μ ≠ ε ∧ ¬ Nm A B V V₂ μ ≤ ballStab 1 p₁ := by
  by_contra hcon
  push Not at hcon
  apply hPU
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  have hVα := goodV_all h α
  have hVα' := goodV_all h α'
  have hle : Nm A B V V₂ α ≤ stab α' := fun n hn =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := ε) (δ := α')
      (dist_eq_one_iff_adj.mpr hα'ε.symm).le (hαε hn)
  have hnot' : ¬ Nm A B V V₂ α' ≤ ballStab 1 α := not_nm_le_symm hVα hVα' hle hnot
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, h1ε, h2ε, h12, hall⟩ := exists_two_others h3 hα'ε
  obtain ⟨k, hkN, hkμ⟩ := h3.exists_smul_of_not_le hα'ε hμ₁ hμ₂ h1ε.symm h2ε.symm h12
    (H := Nm A B V V₂ α) hle (fun n hn => ballStab_le_stab 1 ε (hαε hn)) hnot
  have hkst : (k : D) ∈ stab α' := hle hkN
  have hN12 : ∀ w ∈ Nm A B V V₂ μ₂, ∃ u ∈ Nm A B V V₂ μ₁, ∃ n ∈ Nm A B V V₂ α', w = u * n := by
    intro w hw
    rw [← hkμ, Nm_smul hA hB, mem_conjSub] at hw
    obtain ⟨n, hn, hnw⟩ := conj_mem_mul h hαp hμ₁.symm hα'p hnot'
      ((Nm A B V V₂ α).inv_mem hkN) ((stab α').inv_mem hkst) hw (hcon μ₁ hμ₁ h1ε hw)
    refine ⟨_, hw, n, hn, ?_⟩
    have : (k : D) * ((k : D)⁻¹ * w * (k : D)) * (k : D)⁻¹ = (k : D)⁻¹ * w * (k : D) * n := by
      simpa using hnw
    calc w = (k : D) * ((k : D)⁻¹ * w * (k : D)) * (k : D)⁻¹ := by group
      _ = _ := this
  have hN21 : ∀ w ∈ Nm A B V V₂ μ₁, ∃ u ∈ Nm A B V V₂ μ₂, ∃ n ∈ Nm A B V V₂ α', w = u * n := by
    intro w hw
    have hu : (k : D) * w * (k : D)⁻¹ ∈ Nm A B V V₂ μ₂ := by
      rw [← hkμ, Nm_smul hA hB]
      exact mul_mem_conjSub hw
    obtain ⟨n, hn, hnw⟩ := conj_mem_mul h hαp hμ₂.symm hα'p hnot' hkN hkst hu
      (hcon μ₂ hμ₂ h2ε hu)
    refine ⟨_, hu, n, hn, ?_⟩
    calc w = (k : D)⁻¹ * ((k : D) * w * (k : D)⁻¹) * (k : D) := by group
      _ = _ := hnw
  have hRle : ∀ {m m' : CosetGeom (A ⊔ B) A B}, (graph (A ⊔ B) A B).Adj α' m' →
      (∀ w ∈ Nm A B V V₂ m', ∃ u ∈ Nm A B V V₂ m, ∃ n ∈ Nm A B V V₂ α', w = u * n) →
      ∀ q ∈ ballStab 1 α' ⊓ ballStab 1 m, q ∈ ballStab 1 m' := by
    intro m m' hm' hN q hq
    have hqst : q ∈ stab m' := ballStab_le_stab_of_dist_le (n := 1) (γ := α') (δ := m')
      (dist_eq_one_iff_adj.mpr hm').le hq.1
    refine (goodV_all h m').cent_le q hqst fun w hw => ?_
    obtain ⟨u, hu, n, hn, rfl⟩ := hN w hw
    have h1 : u * q = q * u := (goodV_all h m).qv_cent q hq.2 u hu
    have h2 : n * q = q * n := hVα'.qv_cent q hq.1 n hn
    calc u * n * q = u * (n * q) := by group
      _ = u * (q * n) := by rw [h2]
      _ = (u * q) * n := by group
      _ = (q * u) * n := by rw [h1]
      _ = q * (u * n) := by group
  have hS : ballStab 1 α' ⊓ ballStab 1 μ₁ = ballStab 1 α' ⊓ ballStab 1 μ₂ :=
    le_antisymm (fun q hq => ⟨hq.1, hRle hμ₂ hN12 q hq⟩) (fun q hq => ⟨hq.1, hRle hμ₁ hN21 q hq⟩)
  obtain ⟨g, hgα, hgε⟩ := exists_stab_smul_eq hα'ε hμ₁
  have hginv : g⁻¹ • α' = α' := by rw [inv_smul_eq_iff, hgα]
  have hy : (graph (A ⊔ B) A B).Adj α' (g⁻¹ • μ₂) := by
    have := (smul_adj g⁻¹).mpr hμ₂
    rwa [hginv] at this
  have hyne : g⁻¹ • μ₂ ≠ ε := fun e => h12 (by
    have : μ₂ = g • ε := by rw [← e, smul_inv_smul]
    rw [this, hgε])
  have hyS : ballStab 1 α' ⊓ ballStab 1 (g⁻¹ • μ₂) = ballStab 1 α' ⊓ ballStab 1 μ₁ := by
    rcases hall _ hy with e | e | e
    · exact absurd e hyne
    · rw [e]
    · rw [e, hS]
  have hRε : ballStab 1 α' ⊓ ballStab 1 ε = ballStab 1 α' ⊓ ballStab 1 μ₁ := by
    have e1 := conjSub_ballStab_inf (D := D) g hgα (μ := ε)
    rw [hgε] at e1
    have e2 := conjSub_ballStab_inf (D := D) g⁻¹ hginv (μ := μ₂)
    rw [← hS, ← e1, Subgroup.coe_inv, conjSub_conjSub_inv] at e2
    exact e2.trans hyS
  intro x hx
  apply mem_normalizer_of_conjSub_eq
  have hxα : (⟨x, stab_le α' hx⟩ : ↥(A ⊔ B)) • α' = α' := smul_eq_of_mem_stab hx
  have hxε : (graph (A ⊔ B) A B).Adj α' ((⟨x, stab_le α' hx⟩ : ↥(A ⊔ B)) • ε) := by
    have := (smul_adj (⟨x, stab_le α' hx⟩ : ↥(A ⊔ B))).mpr hα'ε
    rwa [hxα] at this
  have e := conjSub_ballStab_inf (D := D) (⟨x, stab_le α' hx⟩ : ↥(A ⊔ B)) hxα (μ := ε)
  rw [e]
  rcases hall _ hxε with e' | e' | e'
  · rw [e']
  · rw [e', hRε]
  · rw [e', ← hS, hRε]

end GoldAmLab8

end F6

end CFSG.Quasithin
