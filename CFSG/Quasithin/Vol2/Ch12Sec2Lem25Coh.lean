module

public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology

public section

namespace CFSG.Quasithin.H13.Lem25

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem exists_eq_of_isCocycle_of_axis [FiniteDimensional (ZMod 2) E]
    (hE : 3 ≤ finrank (ZMod 2) E) {L : Type*} [Group L] (ρ : L →* (E ≃ₗ[ZMod 2] E))
    (hρ : ∀ (f : Dual (ZMod 2) E) (d : E) (h : f d = 0), ∃ l, ρ l = LinearEquiv.transvection h)
    (δ : L → E) (hδ : ∀ g h, δ (g * h) = δ g + ρ g (δ h)) (hker : ∀ g, ρ g = 1 → δ g = 0)
    {f₀ : Dual (ZMod 2) E} (hf₀ : f₀ ≠ 0)
    (h₀ : ∀ (d : E) (h : f₀ d = 0) g, ρ g = LinearEquiv.transvection h → δ g = 0) :
    ∃ w : E, ∀ g, δ g = ρ g w + w := by
  have hcongr : ∀ g g', ρ g = ρ g' → δ g = δ g' := fun g g' hgg' => by
    have h1 : ρ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, hgg', inv_mul_cancel]
    have h2 := hδ g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hker _ h1, map_zero, add_zero] at h2
    exact h2.symm
  have hsurj : ∀ γ : E ≃ₗ[ZMod 2] E, ∃ l, ρ l = γ := by
    intro γ
    have h1 : Subgroup.closure (LinearEquiv.transvections (ZMod 2) E) ≤ ρ.range := by
      rw [Subgroup.closure_le]
      rintro _ ⟨f, d, h, rfl⟩
      obtain ⟨l, hl⟩ := hρ f d h
      exact ⟨l, hl⟩
    rw [closure_transvections_eq_top] at h1
    exact h1 (Subgroup.mem_top γ)
  choose lift hlift using hρ
  have hspan : ∀ (f : Dual (ZMod 2) E) (d : E) (h : f d = 0), δ (lift f d h) ∈ (ZMod 2) ∙ d := by
    intro f d h
    by_cases hf : f = 0
    · subst hf
      rw [hker _ (by rw [hlift, transvection_zero_form])]
      exact zero_mem _
    obtain ⟨g, -, hg⟩ := exists_comp_eq_of_apply_eq_zero (e₀ := (0 : E)) hf hf₀ (map_zero f)
      (map_zero f₀)
    have hfg : ∀ y, f₀ y = f (g y) := fun y => by rw [← hg]; rfl
    have h₀' : f₀ (g.symm d) = 0 := by rw [hfg, LinearEquiv.apply_symm_apply, h]
    obtain ⟨l, hl⟩ := hsurj g
    set k := l * lift f₀ (g.symm d) h₀' * l⁻¹ with hkdef
    have hk : ρ k = LinearEquiv.transvection h := by
      rw [hkdef, map_mul, map_mul, map_inv, hl, hlift,
        mul_transvection_mul_inv g h₀' (transvection_comp_apply_eq_zero g h₀')]
      ext x
      rw [transvection_apply, transvection_apply, LinearEquiv.apply_symm_apply]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hfg, LinearEquiv.apply_symm_apply]
    have e1 := hcongr (lift f d h) k (by rw [hlift, hk])
    have e2 : δ (k * l) = δ l := by
      rw [show k * l = l * lift f₀ (g.symm d) h₀' by rw [hkdef]; group, hδ,
        h₀ _ h₀' _ (hlift _ _ _), map_zero, add_zero]
    rw [hδ, hk, transvection_apply] at e2
    have e3 : δ k = -(f (δ l) • d) := by
      rw [eq_sub_of_add_eq e2]
      abel
    rw [e1, e3]
    exact neg_mem (smul_mem _ _ (mem_span_singleton_self d))
  choose c hc using fun f d h => mem_span_singleton.1 (hspan f d h)
  have haxis : ∀ (f : Dual (ZMod 2) E) (d d' : E) (h : f d = 0) (h' : f d' = 0), d ≠ 0 →
      d' ≠ 0 → c f d h = c f d' h' := by
    intro f d d' h h' hd hd'
    by_cases hdd' : d = d'
    · subst hdd'
      rfl
    have h'' : f (d + d') = 0 := by rw [map_add, h, h', add_zero]
    have h1 := hcongr (lift f d h * lift f d' h') (lift f (d + d') h'')
      (by rw [map_mul, hlift, hlift, hlift, transvection_mul_transvection_left])
    rw [hδ, hlift, ← hc, ← hc, ← hc, transvection_apply, map_smul, h', smul_zero, zero_smul,
      add_zero, smul_add] at h1
    have h2 : (c f d h + c f (d + d') h'') • d + (c f d' h' + c f (d + d') h'') • d' = 0 := by
      have : (c f d h + c f (d + d') h'') • d + (c f d' h' + c f (d + d') h'') • d' =
          (c f d h • d + c f d' h' • d') + (c f (d + d') h'' • d + c f (d + d') h'' • d') := by
        rw [add_smul, add_smul]
        abel
      rw [this, h1, two_add_self]
    obtain ⟨e1, e2⟩ := eq_zero_of_smul_add_smul_eq_zero hd hd' hdd' h2
    have hz : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    rw [hz _ _ e1, hz _ _ e2]
  have hcentre : ∀ (f f' : Dual (ZMod 2) E) (d : E) (h : f d = 0) (h' : f' d = 0)
      (h'' : (f + f') d = 0), d ≠ 0 → c (f + f') d h'' = c f d h + c f' d h' := by
    intro f f' d h h' h'' hd
    have h1 := hcongr (lift f d h * lift f' d h') (lift (f + f') d h'')
      (by rw [map_mul, hlift, hlift, hlift, transvection_mul_transvection_right])
    rw [hδ, hlift, ← hc, ← hc, ← hc, transvection_apply, map_smul, h, smul_zero, zero_smul,
      add_zero, ← add_smul] at h1
    exact (smul_eq_smul_of_ne_zero hd h1).symm
  have hne : ∀ f : Dual (ZMod 2) E, ∃ d, f d = 0 ∧ d ≠ 0 := fun f => by
    obtain ⟨d, hd, hd0⟩ := exists_ne_zero_mem_of_finrank_pos (U := LinearMap.ker f)
      (by have := finrank_ker_add_one_ge f; omega)
    exact ⟨d, hd, hd0⟩
  choose dsel hdsel hdsel0 using hne
  let e : Dual (ZMod 2) E → ZMod 2 := fun f => c f (dsel f) (hdsel f)
  have he : ∀ (f : Dual (ZMod 2) E) (d : E) (h : f d = 0), d ≠ 0 → c f d h = e f :=
    fun f d h hd => haxis f d (dsel f) h (hdsel f) hd (hdsel0 f)
  have hadd : ∀ f f', e (f + f') = e f + e f' := by
    intro f f'
    obtain ⟨d, hd, hd0⟩ := exists_ne_zero_mem_of_finrank_pos
      (U := LinearMap.ker f ⊓ LinearMap.ker f')
      (by have := finrank_ker_inf_ker_add_two_ge f f'; omega)
    have hf : f d = 0 := hd.1
    have hf' : f' d = 0 := hd.2
    have hff' : (f + f') d = 0 := by rw [LinearMap.add_apply, hf, hf', add_zero]
    rw [← he _ _ hff' hd0, ← he _ _ hf hd0, ← he _ _ hf' hd0]
    exact hcentre f f' d hf hf' hff' hd0
  let eAdd : Dual (ZMod 2) E →+ ZMod 2 :=
    { toFun := e
      map_zero' := by
        have := hadd 0 0
        rw [add_zero] at this
        exact (by decide : ∀ a : ZMod 2, a = a + a → a = 0) _ this
      map_add' := hadd }
  let eLin : Dual (ZMod 2) (Dual (ZMod 2) E) := eAdd.toZModLinearMap 2
  let w : E := (Module.evalEquiv (ZMod 2) E).symm eLin
  have hw : ∀ f : Dual (ZMod 2) E, f w = e f := fun f => by
    have h1 : Module.evalEquiv (ZMod 2) E w = eLin := LinearEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun φ : Dual (ZMod 2) (Dual (ZMod 2) E) => φ f) h1
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply] at h2
    exact h2
  refine ⟨w, ?_⟩
  let δ' : L → E := fun g => δ g + ρ g w + w
  have hδ' : ∀ g h, δ' (g * h) = δ' g + ρ g (δ' h) := fun g h => by
    simp only [δ', hδ, map_mul, LinearEquiv.mul_apply, map_add]
    calc δ g + ρ g (δ h) + ρ g (ρ h w) + w
        = δ g + ρ g (δ h) + ρ g (ρ h w) + w + (ρ g w + ρ g w) := by
          rw [two_add_self (ρ g w), add_zero]
      _ = _ := by abel
  have hcongr' : ∀ g g', ρ g = ρ g' → δ' g = δ' g' := fun g g' hgg' => by
    simp only [δ']
    rw [hcongr g g' hgg', hgg']
  have hlift' : ∀ (f : Dual (ZMod 2) E) (d : E) (h : f d = 0) g,
      ρ g = LinearEquiv.transvection h → δ' g = 0 := by
    intro f d h g hg
    rw [hcongr' g (lift f d h) (by rw [hg, hlift])]
    simp only [δ']
    rw [← hc, hlift, transvection_apply]
    by_cases hd : d = 0
    · subst hd
      rw [smul_zero, smul_zero, add_zero, zero_add, two_add_self]
    · rw [he f d h hd, hw f]
      calc e f • d + (w + e f • d) + w = (e f • d + e f • d) + (w + w) := by abel
        _ = 0 := by rw [two_add_self, two_add_self, add_zero]
  have hall : ∀ γ : E ≃ₗ[ZMod 2] E, ∃ g, ρ g = γ ∧ δ' g = 0 := by
    intro γ
    have hγ : γ ∈ Subgroup.closure (LinearEquiv.transvections (ZMod 2) E) := by
      rw [closure_transvections_eq_top]
      exact Subgroup.mem_top γ
    induction hγ using Subgroup.closure_induction with
    | mem γ hγ =>
      obtain ⟨f, d, h, rfl⟩ := hγ
      exact ⟨lift f d h, hlift f d h, hlift' f d h _ (hlift f d h)⟩
    | one =>
      refine ⟨1, map_one ρ, ?_⟩
      simp only [δ', hker 1 (map_one ρ), map_one, zero_add]
      exact two_add_self w
    | mul γ₁ γ₂ _ _ ih₁ ih₂ =>
      obtain ⟨g₁, hg₁, hg₁'⟩ := ih₁
      obtain ⟨g₂, hg₂, hg₂'⟩ := ih₂
      refine ⟨g₁ * g₂, by rw [map_mul, hg₁, hg₂], ?_⟩
      rw [hδ', hg₁', hg₂', map_zero, add_zero]
    | inv γ _ ih =>
      obtain ⟨g, hg, hg'⟩ := ih
      refine ⟨g⁻¹, by rw [map_inv, hg], ?_⟩
      have h1 := hδ' g g⁻¹
      rw [mul_inv_cancel, hg', zero_add] at h1
      have h0 : δ' 1 = 0 := by
        simp only [δ', hker 1 (map_one ρ), map_one, zero_add]
        exact two_add_self w
      rw [h0] at h1
      exact (ρ g).injective (by rw [← h1, map_zero])
  intro g
  obtain ⟨g', hg', hg''⟩ := hall (ρ g)
  have h1 := hcongr' g g' hg'.symm
  rw [hg''] at h1
  simp only [δ'] at h1
  rw [two_add_eq_iff, zero_add, two_add_eq_iff] at h1
  rw [h1, add_comm]

end CFSG.Quasithin.H13.Lem25
