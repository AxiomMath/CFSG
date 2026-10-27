module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Lab

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem fx_base0 (h : TwoSys A B z V c V₂) {x : D}
    (hx : x ∈ Fx V V₂ (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B)) : x = 1 ∨ x = z := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hn' : IsNaturalAt A (B ⊓ A) z V := by
    have := h.nat
    rwa [inf_comm] at this
  rw [mem_Fx, Nm_γ₀ hA, stab_γ₁ le_sup_right, stab_γ₀ le_sup_left] at hx
  have hx2 : ∀ t ∈ A ⊓ B, x * t = t * x := fun t ht => (hx.2 t ht).symm
  exact eq_one_or_of_centralizes h.gold.symm hn' hx.1 hx2

theorem fx_base1 (h : TwoSys A B z V c V₂) {x : D}
    (hx : x ∈ Fx V V₂ (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B)) : x = 1 ∨ x = c := by
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  rw [mem_Fx, Nm_γ₁ hB, stab_γ₁ le_sup_right, stab_γ₀ le_sup_left] at hx
  exact eq_one_or_of_centralizes h.gold h.nat₂ hx.1 fun t ht => (hx.2 t ht).symm

omit [Finite D] in
theorem fx_cent_smul (hA : A ≤ Subgroup.normalizer (V : Set D))
    (hB : B ≤ Subgroup.normalizer (V₂ : Set D)) (k : ↥(A ⊔ B)) {γ δ : CosetGeom (A ⊔ B) A B}
    (hbase : ∀ x ∈ Fx V V₂ γ δ, ∀ g ∈ stab δ, g * x * g⁻¹ = x) :
    ∀ x ∈ Fx V V₂ (k • γ) (k • δ), ∀ g ∈ stab (k • δ), g * x * g⁻¹ = x := by
  intro x hx g hg
  rw [mem_Fx_smul hA hB] at hx
  rw [stab_smul, mem_conjSub] at hg
  have := hbase _ hx _ hg
  calc g * x * g⁻¹ = (k : D) * (((k : D)⁻¹ * g * k) * ((k : D)⁻¹ * x * k) *
        ((k : D)⁻¹ * g * k)⁻¹) * (k : D)⁻¹ := by group
    _ = (k : D) * ((k : D)⁻¹ * x * k) * (k : D)⁻¹ := by rw [this]
    _ = x := by group

theorem fx_cent (h : TwoSys A B z V c V₂) (hz : ∀ y ∈ B, y * z * y⁻¹ = z)
    (hc : ∀ a ∈ A, a * c * a⁻¹ = c) {γ δ : CosetGeom (A ⊔ B) A B}
    (hadj : (graph (A ⊔ B) A B).Adj γ δ) {x : D} (hx : x ∈ Fx V V₂ γ δ) {g : D}
    (hg : g ∈ stab δ) : g * x * g⁻¹ = x := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_smul_edge hadj
  · refine fx_cent_smul hA hB k ?_ x hx g hg
    intro x' hx' g' hg'
    rw [stab_γ₁ le_sup_right] at hg'
    rcases fx_base0 h hx' with e | e
    · rw [e]; group
    · rw [e]; exact hz g' hg'
  · refine fx_cent_smul hA hB k ?_ x hx g hg
    intro x' hx' g' hg'
    rw [stab_γ₀ le_sup_left] at hg'
    rcases fx_base1 h hx' with e | e
    · rw [e]; group
    · rw [e]; exact hc g' hg'

theorem fx_mem_of_adj (h : TwoSys A B z V c V₂) (hz : ∀ y ∈ B, y * z * y⁻¹ = z)
    (hc : ∀ a ∈ A, a * c * a⁻¹ = c) {p x x' : CosetGeom (A ⊔ B) A B}
    (hx : (graph (A ⊔ B) A B).Adj x p) (hx' : (graph (A ⊔ B) A B).Adj x' p) {t : D}
    (ht : t ∈ Fx V V₂ x p) : t ∈ Fx V V₂ x' p := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  obtain ⟨a, hap, hax⟩ := exists_stab_smul_eq hx.symm hx'.symm
  have hap' : (a : D) ∈ stab p := mem_stab_of_smul_eq hap
  have hfix : (a : D) * t * (a : D)⁻¹ = t := fx_cent h hz hc hx ht hap'
  have hmem : (a : D) * t * (a : D)⁻¹ ∈ Fx V V₂ (a • x) (a • p) := by
    rw [mem_Fx_smul hA hB]
    have e : (a : D)⁻¹ * ((a : D) * t * (a : D)⁻¹) * a = t := by group
    rw [e]
    exact ht
  rw [hap, hax, hfix] at hmem
  exact hmem

theorem fx_inf_fx_eq_one (h : TwoSys A B z V c V₂) {δ₂ δ₁ δ₃ : CosetGeom (A ⊔ B) A B}
    (h1 : (graph (A ⊔ B) A B).Adj δ₂ δ₁) (h3 : (graph (A ⊔ B) A B).Adj δ₂ δ₃) (hne : δ₁ ≠ δ₃)
    {t : D} (t1 : t ∈ Fx V V₂ δ₂ δ₁) (t3 : t ∈ Fx V V₂ δ₂ δ₃) : t = 1 := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  by_contra ht1
  obtain ⟨a, ha2, ha1⟩ := exists_stab_smul_eq h1 h3
  have ha2' : (a : D) ∈ stab δ₂ := mem_stab_of_smul_eq ha2
  have hmem : (a : D) * t * (a : D)⁻¹ ∈ Fx V V₂ (a • δ₂) (a • δ₁) := by
    rw [mem_Fx_smul hA hB]
    have e : (a : D)⁻¹ * ((a : D) * t * (a : D)⁻¹) * a = t := by group
    rw [e]
    exact t1
  rw [ha2, ha1] at hmem
  obtain ⟨w, -, -, hw⟩ := (goodE0_all h h3).lab
  have hat1 : (a : D) * t * (a : D)⁻¹ ≠ 1 := fun e => ht1 (by
    calc t = (a : D)⁻¹ * ((a : D) * t * (a : D)⁻¹) * a := by group
      _ = 1 := by rw [e]; group)
  have e1 := (hw t t3).resolve_left ht1
  have e2 := (hw _ hmem).resolve_left hat1
  have hfix : (a : D) * t * (a : D)⁻¹ = t := e2.trans e1.symm
  have hst : (a : D) ∈ stab δ₁ := fx_moved h h1 t1 ht1 ha2' hfix
  have hfix1 : a • δ₁ = δ₁ := smul_eq_of_mem_stab (g := a) hst
  exact hne (hfix1.symm.trans ha1)

end GoldAmLab7

end F6

end CFSG.Quasithin
