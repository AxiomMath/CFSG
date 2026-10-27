module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts
public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

section Transport

variable {Γ Δ : Type} [Group Γ] [Group Δ]

theorem kmap_pCore_mem (Ω : Subgroup Γ) (e : ↥Ω ≃* Δ) (H : Subgroup Γ) {γ : Γ}
    (hγΩ : γ ∈ Ω) (hγ : γ ∈ pCoreOf 2 (H ⊓ Ω)) :
    (⟨γ, hγΩ⟩ : ↥Ω) ∈ pCoreOf 2 (H.subgroupOf Ω) ∧
      e ⟨γ, hγΩ⟩ ∈ pCoreOf 2 ((H.subgroupOf Ω).map e.toMonoidHom) := by
  have hsub : (H.subgroupOf Ω).map Ω.subtype = H ⊓ Ω := Subgroup.subgroupOf_map_subtype H Ω
  have hcore : pCoreOf 2 (H ⊓ Ω) = (pCoreOf 2 (H.subgroupOf Ω)).map Ω.subtype := by
    rw [← hsub]
    exact CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 Ω.subtype Subtype.val_injective _
  rw [hcore] at hγ
  obtain ⟨x, hx, hxγ⟩ := Subgroup.mem_map.1 hγ
  have hx' : x = ⟨γ, hγΩ⟩ := Subtype.ext hxγ
  rw [hx'] at hx
  refine ⟨hx, ?_⟩
  have hmap := CFSG.Quasithin.H.ZTrans.pCoreOf_map_of_injective 2 e.toMonoidHom e.injective
    (H.subgroupOf Ω)
  rw [hmap]
  exact Subgroup.mem_map_of_mem _ hx

theorem eq_of_fpf [Finite Δ] {D₀ H : Subgroup Δ} (hcard : Nat.card D₀ = 4) (hH : H ≤ D₀) (hHne : H ≠ ⊥)
    {g : Δ} (hg3 : g ^ 3 = 1) (hgH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hfpf : ∀ d ∈ D₀, g * d * g⁻¹ = d → d = 1) : H = D₀ := by
  obtain ⟨d, hdH, hd1⟩ : ∃ d ∈ H, d ≠ 1 := by
    by_contra h
    push Not at h
    exact hHne ((Subgroup.eq_bot_iff_forall H).2 h)
  have hdD : d ∈ D₀ := hH hdH
  have conj_ne : ∀ x : Δ, x ≠ 1 → g * x * g⁻¹ ≠ 1 := by
    intro x hx h
    apply hx
    have h1 : g * x = g := mul_inv_eq_one.1 h
    exact mul_left_cancel (h1.trans (mul_one g).symm)
  have h3' : g * (g * g) = 1 := by
    rw [← pow_three]
    exact hg3
  have conj3 : ∀ x : Δ, g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
    intro x
    have e : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * (g * g)) * x * (g * (g * g))⁻¹ := by
      group
    rw [e, h3']
    simp
  set e1 := g * d * g⁻¹ with he1
  set e2 := g * e1 * g⁻¹ with he2
  have he1H : e1 ∈ H := hgH d hdH
  have he2H : e2 ∈ H := hgH e1 he1H
  have he1D : e1 ∈ D₀ := hH he1H
  have he1_ne : e1 ≠ 1 := conj_ne d hd1
  have he2_ne : e2 ≠ 1 := conj_ne e1 he1_ne
  have hA : e1 ≠ d := fun h => hd1 (hfpf d hdD h)
  have hD : e2 ≠ d := by
    intro h
    apply hA
    have hx : g * e2 * g⁻¹ = e1 := by rw [h]
    have c3 := conj3 e1
    rw [← he2, hx] at c3
    have : e2 = e1 := by rw [he2]; exact c3
    exact (h.symm.trans this).symm
  have hE : e1 ≠ e2 := by
    intro h
    have hfix : g * e1 * g⁻¹ = e1 := by rw [← he2, ← h]
    exact he1_ne (hfpf e1 he1D hfix)
  have hcard3 : 3 ≤ Nat.card H := by
    let f : Fin 3 → H := ![⟨d, hdH⟩, ⟨e1, he1H⟩, ⟨e2, he2H⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢
      · exact hA hij.symm
      · exact hD hij.symm
      · exact hA hij
      · exact hE hij
      · exact hD hij
      · exact hE hij.symm
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hdvd : Nat.card H ∣ 4 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hH
  have h4 : Nat.card H = 4 := by
    have hle : Nat.card H ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card H <;> omega
  exact Subgroup.eq_of_le_of_card_ge hH (by rw [hcard, h4])

end Transport

section D0

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]

theorem card_D0 (F2 : FactF2) (hI : Module.finrank (ZMod 2) I = 4)
    (p ℓ Pl : Submodule (ZMod 2) I) (hp : Module.finrank (ZMod 2) p = 1)
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hPl : Module.finrank (ZMod 2) Pl = 3)
    (hpℓ : p < ℓ) (hℓPl : ℓ < Pl)
    (Y₂ : Subgroup (I ≃ₗ[ZMod 2] I)) (hY₂ : Y₂ = stabS p ∨ Y₂ = stabS Pl) :
    Nat.card ↥(pCoreOf 2 Y₂ ⊓ pCoreOf 2 (stabS ℓ)) = 4 := by
  obtain ⟨h1, h2⟩ := F2 I hI p ℓ Pl hp hℓ hPl hpℓ hℓPl
  rcases hY₂ with rfl | rfl
  · exact h1.1
  · exact h2.1

theorem fpf_D0 (F3 : FactF3) (hI : Module.finrank (ZMod 2) I = 4)
    (p ℓ Pl : Submodule (ZMod 2) I) (hp : Module.finrank (ZMod 2) p = 1)
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hPl : Module.finrank (ZMod 2) Pl = 3)
    (hpℓ : p < ℓ) (hℓPl : ℓ < Pl)
    (Y₂ : Subgroup (I ≃ₗ[ZMod 2] I)) (hY₂ : Y₂ = stabS p ∨ Y₂ = stabS Pl)
    {g : I ≃ₗ[ZMod 2] I} (hg3 : orderOf g = 3) (hgY₁ : g ∈ stabS ℓ) (hgY₂ : g ∈ Y₂) :
    ∀ d ∈ pCoreOf 2 Y₂ ⊓ pCoreOf 2 (stabS ℓ), g * d * g⁻¹ = d → d = 1 := by
  obtain ⟨h1, h2⟩ := F3 I hI p ℓ Pl hp hℓ hPl hpℓ hℓPl g hg3
  rcases hY₂ with rfl | rfl
  · exact (h1 hgY₂ hgY₁).2.2
  · exact h2 hgY₁ hgY₂

end D0

end CFSG.Quasithin.H13.C1294
