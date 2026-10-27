module

public import CFSG.LocalAnalysis.StandardType.GGWAutDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLinRefl_iff_isReflLin {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (r : V ≃ₗ[ZMod 3] V) : GGLinRefl r ↔ IsReflLin r := by
  constructor
  · rintro ⟨hr2, hr1⟩
    have hM_ne : ggLinMove r ≠ ⊥ := by
      intro hbot
      have h0 : Module.finrank (ZMod 3) (ggLinMove r) = 0 := by rw [hbot]; simp
      omega
    obtain ⟨c, hcM, hc0⟩ := (Submodule.ne_bot_iff (ggLinMove r)).mp hM_ne
    have hM_eq : ggLinMove r = ZMod 3 ∙ c :=
      eq_span_singleton_of_mem_of_finrank_eq_one hr1 hcM hc0
    let L : V →ₗ[ZMod 3] V := r.toLinearMap - LinearMap.id
    let g : V →ₗ[ZMod 3] (ZMod 3 ∙ c) :=
      L.codRestrict (ZMod 3 ∙ c) (fun v => by
        rw [← hM_eq]
        exact ⟨v, rfl⟩)
    let φ : Module.Dual (ZMod 3) V := (LinearEquiv.coord (ZMod 3) V c hc0).toLinearMap.comp g
    have hφv : ∀ v, φ v • c = L v := by
      intro v
      have := LinearEquiv.coord_apply_smul (ZMod 3) V c hc0 (g v)
      simp [φ, g, L, LinearMap.comp_apply]
    have hr_apply : ∀ v, r v = v + φ v • c := by
      intro v
      rw [hφv v]
      simp only [L, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
      abel
    have hc_range : c ∈ LinearMap.range L := by
      change c ∈ ggLinMove r
      rw [hM_eq]
      exact Submodule.mem_span_singleton_self c
    obtain ⟨w, hw⟩ := hc_range
    have hw' : c = r w - w := by
      rw [← hw]
      simp only [L, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
    have hrr : r (r w) = w := by
      have := congrArg (fun f : V ≃ₗ[ZMod 3] V => f w) hr2
      simpa using this
    have hrc : r c = -c := by
      calc r c = r (r w - w) := by rw [hw']
        _ = r (r w) - r w := by rw [map_sub]
        _ = w - r w := by rw [hrr]
        _ = -(r w - w) := by abel
        _ = -c := by rw [← hw']
    have hφc : φ c = -2 := by
      have h1 : φ c • c = (-2 : ZMod 3) • c := by
        calc φ c • c = (c + φ c • c) - c := by abel
          _ = r c - c := by rw [← hr_apply c]
          _ = -c - c := by rw [hrc]
          _ = (-2 : ZMod 3) • c := by module
      exact smul_left_injective (ZMod 3) hc0 h1
    refine ⟨c, -φ, ?_, ?_⟩
    · rw [LinearMap.neg_apply, hφc]
      norm_num
    · ext v
      rw [Module.reflection_apply, hr_apply v]
      simp [LinearMap.neg_apply]
  · rintro ⟨c, φ, h, rfl⟩
    constructor
    · ext v
      exact Module.involutive_reflection h v
    · have hc0 : c ≠ 0 := by
        intro hc
        have h0 : φ c = 0 := by rw [hc, map_zero]
        rw [h] at h0
        exact two_ne_zero_of_charP_three (K := ZMod 3) h0
      have hrange : ggLinMove (Module.reflection h) = ZMod 3 ∙ c := by
        rw [ggLinMove]
        apply le_antisymm
        · intro v hv
          obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hv
          rw [← hw, Submodule.mem_span_singleton]
          refine ⟨-(φ w), ?_⟩
          simp only [LinearEquiv.coe_toLinearMap, LinearMap.sub_apply, LinearMap.id_apply,
            Module.reflection_apply]
          rw [neg_smul]
          abel
        · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_range]
          refine ⟨c, ?_⟩
          simp only [LinearEquiv.coe_toLinearMap, LinearMap.sub_apply, LinearMap.id_apply,
            Module.reflection_apply, h]
          rw [show (2 : ZMod 3) = -1 by decide, neg_smul]
          module
      rw [hrange, finrank_span_singleton hc0]

section Common

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggWAut_reflGp_le (A : Subgroup (V ≃ₗ[ZMod 3] V)) : reflGp A ≤ A := by
  rw [reflGp]
  exact (Subgroup.closure_le A).mpr (fun t ht => ht.1)

theorem ggWAut_reflGp_conj (A : Subgroup (V ≃ₗ[ZMod 3] V)) {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ A)
    {r : V ≃ₗ[ZMod 3] V} (hr : r ∈ reflGp A) : a * r * a⁻¹ ∈ reflGp A := by
  rw [reflGp] at hr ⊢
  refine Subgroup.closure_induction
    (p := fun x _ => a * x * a⁻¹ ∈ Subgroup.closure {t | t ∈ A ∧ IsReflLin t})
    (fun t ht => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ih => ?_) hr
  · exact Subgroup.subset_closure ⟨A.mul_mem (A.mul_mem ha ht.1) (A.inv_mem ha),
      ggQ2_isReflLin_conj a t ht.2⟩
  · simp
  · rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  · rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ih

theorem ggWAut_reflGp_closure (A : Subgroup (V ≃ₗ[ZMod 3] V)) :
    reflGp A = Subgroup.closure {r | r ∈ reflGp A ∧ GGLinRefl r} := by
  apply le_antisymm
  · rw [reflGp]
    apply (Subgroup.closure_le (Subgroup.closure {r | r ∈ reflGp A ∧ GGLinRefl r})).mpr
    intro t ht
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ht,
      (ggLinRefl_iff_isReflLin t).mpr ht.2⟩
  · rw [reflGp]
    apply (Subgroup.closure_le (Subgroup.closure {t | t ∈ A ∧ IsReflLin t})).mpr
    intro t ht
    exact ht.1

theorem ggWAut_schur_pm (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R)
    (T : V ≃ₗ[ZMod 3] V) (hT : ∀ r ∈ R, T * r = r * T) :
    (∀ v, T v = v) ∨ (∀ v, T v = -v) := by
  have hcomm : ∀ a ∈ R, T.toLinearMap ∘ₗ (a : V →ₗ[ZMod 3] V) =
      (a : V →ₗ[ZMod 3] V) ∘ₗ T.toLinearMap := by
    intro a ha
    ext v
    exact congrArg (fun f : V ≃ₗ[ZMod 3] V => f v) (hT a ha)
  obtain ⟨c, hc⟩ := habs.2 T.toLinearMap hcomm
  by_cases hsub : Subsingleton V
  · exact Or.inl fun v => Subsingleton.elim _ _
  · have hc0 : c ≠ 0 := by
      intro hc0
      obtain ⟨x, y, hxy⟩ := not_subsingleton_iff_nontrivial.mp hsub
      apply hxy
      apply T.injective
      have hx : T x = 0 := by
        have := congrArg (fun f : V →ₗ[ZMod 3] V => f x) hc
        rw [hc0, zero_smul] at this
        simpa using this
      have hy : T y = 0 := by
        have := congrArg (fun f : V →ₗ[ZMod 3] V => f y) hc
        rw [hc0, zero_smul] at this
        simpa using this
      rw [hx, hy]
    have hc_eq : c = 1 ∨ c = -1 := by
      have hc2 : c ^ 2 = 1 := by
        have := ZMod.pow_card_sub_one_eq_one (p := 3) (a := c) hc0
        simpa using this
      have hfac : (c - 1) * (c + 1) = 0 := by
        have : c ^ 2 - 1 = 0 := by rw [hc2, sub_self]
        rwa [show (c - 1) * (c + 1) = c ^ 2 - 1 by ring]
      rcases mul_eq_zero.mp hfac with h | h
      · left; exact sub_eq_zero.mp h
      · right; exact eq_neg_of_add_eq_zero_left h
    rcases hc_eq with h1 | h1
    · left; intro v
      have := congrArg (fun f : V →ₗ[ZMod 3] V => f v) hc
      rw [h1, one_smul] at this
      simpa using this
    · right; intro v
      have := congrArg (fun f : V →ₗ[ZMod 3] V => f v) hc
      rw [h1, neg_smul, one_smul] at this
      simpa using this

theorem ggWAut_pm_of_conj (A R : Subgroup (V ≃ₗ[ZMod 3] V)) (hR : R = reflGp A)
    (habs : ZS.AbsIrred 3 R) {a : V ≃ₗ[ZMod 3] V} (_ha : a ∈ A) {w : V ≃ₗ[ZMod 3] V} (_hw : w ∈ R)
    (h : ∀ r ∈ R, IsReflLin r → a * r * a⁻¹ = w * r * w⁻¹) :
    (∀ v, a v = w v) ∨ (∀ v, a v = -(w v)) := by
  have hconj : ∀ x ∈ R, a * x * a⁻¹ = w * x * w⁻¹ := by
    intro x hx
    have hx' : x ∈ reflGp A := by rwa [← hR]
    rw [reflGp] at hx'
    refine Subgroup.closure_induction (p := fun x _ => a * x * a⁻¹ = w * x * w⁻¹)
      (fun t ht => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ih => ?_) hx'
    · exact h t (by rw [hR]; exact Subgroup.subset_closure ht) ht.2
    · group
    · rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group,
          show w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) by group, ihx, ihy]
    · rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group,
          show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group, ih]
  have hTcomm : ∀ x ∈ R, (w⁻¹ * a) * x = x * (w⁻¹ * a) := by
    intro x hx
    have h1 : a * x * a⁻¹ = w * x * w⁻¹ := hconj x hx
    calc (w⁻¹ * a) * x = w⁻¹ * (a * x * a⁻¹) * a := by group
      _ = w⁻¹ * (w * x * w⁻¹) * a := by rw [h1]
      _ = x * (w⁻¹ * a) := by group
  rcases ggWAut_schur_pm R habs (w⁻¹ * a) hTcomm with h1 | h1
  · left; intro v
    have := congrArg (fun x : V => w x) (h1 v)
    simpa using this
  · right; intro v
    have := congrArg (fun x : V => w x) (h1 v)
    simpa using this

theorem ggWAut_absIrred_of_le {R R' : Subgroup (V ≃ₗ[ZMod 3] V)} (h : R ≤ R')
    (habs : ZS.AbsIrred 3 R) : ZS.AbsIrred 3 R' := by
  refine ⟨?_, ?_⟩
  · intro W hW
    exact habs.1 W (fun a ha w hw => hW a (h ha) w hw)
  · intro T hT
    exact habs.2 T (fun a ha => hT a (h ha))

end Common

theorem ggWAut_SL_has_transvection {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (hn : 2 ≤ Module.finrank (ZMod 3) V)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (h : ∀ g : V ≃ₗ[ZMod 3] V, LinearEquiv.det g = 1 → g ∈ A) :
    ¬ TransvectionFree A := by
  intro hTF
  obtain ⟨u, ψ, hu, hψ, hψu⟩ : ∃ (u : V) (ψ : Module.Dual (ZMod 3) V),
      u ≠ 0 ∧ ψ ≠ 0 ∧ ψ u = 0 := by
    let b := Module.finBasis (ZMod 3) V
    let i0 : Fin (Module.finrank (ZMod 3) V) := ⟨0, by omega⟩
    let i1 : Fin (Module.finrank (ZMod 3) V) := ⟨1, by omega⟩
    refine ⟨b i0, b.coord i1, b.ne_zero i0, ?_, ?_⟩
    · intro h0
      have := congrArg (fun ψ : Module.Dual (ZMod 3) V => ψ (b i1)) h0
      simp [i1] at this
    · simp [i0, i1]
  let N : V →ₗ[ZMod 3] V := ψ.smulRight u
  have hN2v : ∀ v, N (N v) = 0 := by
    intro v
    simp [N, LinearMap.smulRight_apply, hψu]
  have hfg : (LinearMap.id + N).comp (LinearMap.id - N) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [map_sub, hN2v v]; abel
  have hgf : (LinearMap.id - N).comp (LinearMap.id + N) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply]
    rw [map_add, hN2v v]; abel
  let g : V ≃ₗ[ZMod 3] V := LinearEquiv.ofLinearMap (LinearMap.id + N) (LinearMap.id - N) hfg hgf
  have hg_apply : ∀ v, g v = v + ψ v • u := by
    intro v
    simp [g, N, LinearMap.smulRight_apply]
  have hN2 : N ^ 2 = 0 := by
    rw [pow_two]
    ext v
    exact hN2v v
  have h3N : (3 : ZMod 3) = 0 := by decide
  have hg3 : g ^ 3 = 1 := by
    ext v
    simp only [LinearEquiv.pow_apply, Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq, LinearEquiv.coe_one]
    simp only [hg_apply]
    simp only [map_add, map_smul, hψu, smul_zero, add_zero]
    rw [show v + ψ v • u + ψ v • u + ψ v • u = v + (3 : ZMod 3) • (ψ v • u) by module]
    rw [h3N, zero_smul, add_zero]
  have hdet : LinearEquiv.det g = 1 := by
    have h4 : (LinearEquiv.det g) ^ 3 = 1 := by
      rw [← map_pow (LinearEquiv.det : (V ≃ₗ[ZMod 3] V) →* (ZMod 3)ˣ) g 3, hg3, map_one]
    have h5 : (LinearEquiv.det g : ZMod 3) ^ 3 = 1 := by
      have := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) h4
      simpa using this
    rw [ZMod.pow_card] at h5
    exact Units.ext h5
  have hgA : g ∈ A := h g hdet
  exact (hTF g hgA) ⟨u, ψ, hu, hψ, hψu, hg_apply⟩

end CFSG.StandardType

end
