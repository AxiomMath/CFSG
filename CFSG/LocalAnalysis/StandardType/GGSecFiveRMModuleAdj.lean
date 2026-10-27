module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

private lemma exists_span_and_repr_of_ggLinRefl
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {r : V ≃ₗ[ZMod p] V} (hr : GGLinRefl r) :
    ∃ (e : V) (f : Module.Dual (ZMod p) V), e ≠ 0 ∧ ggLinMove r = ZMod p ∙ e ∧
      f e = 2 ∧ ∀ v, r v = v - f v • e := by
  obtain ⟨hr2, hrank⟩ := hr
  have hUatom : IsAtom (ggLinMove r) := Submodule.isAtom_iff_finrank_eq_one.mpr hrank
  obtain ⟨e, heU, he0⟩ := (ggLinMove r).ne_bot_iff.mp hUatom.ne_bot
  have hspan : ggLinMove r = ZMod p ∙ e :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrank heU he0
  have hrr : ∀ v, r (r v) = v := by
    intro v
    have h := congrArg (fun T : V ≃ₗ[ZMod p] V => T v) hr2
    simpa [LinearEquiv.mul_apply] using h
  let N : V →ₗ[ZMod p] V := r.toLinearMap - LinearMap.id
  have here : r e = -e := by
    have heU' : e ∈ LinearMap.range N := by
      simpa only [ggLinMove, N] using heU
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp heU'
    have hw' : r w - w = e := by simpa [N] using hw
    calc r e = r (r w - w) := by rw [hw']
      _ = r (r w) - r w := by rw [map_sub]
      _ = w - r w := by rw [hrr w]
      _ = -(r w - w) := by abel
      _ = -e := by rw [hw']
  let G : V →ₗ[ZMod p] V := LinearMap.id - r.toLinearMap
  have hGmem : ∀ v, G v ∈ ZMod p ∙ e := by
    intro v
    rw [← hspan]
    have : G v = -(N v) := by
      simp only [G, N, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
      abel
    rw [this]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self N v)
  let G' : V →ₗ[ZMod p] (ZMod p ∙ e) := G.codRestrict (ZMod p ∙ e) hGmem
  let f : V →ₗ[ZMod p] ZMod p := (LinearEquiv.coord (ZMod p) V e he0).comp G'
  have hf : ∀ v, f v • e = G v := by
    intro v
    change (LinearEquiv.coord (ZMod p) V e he0 (G' v)) • e = G v
    rw [LinearEquiv.coord_apply_smul]
    rfl
  refine ⟨e, f, he0, hspan, ?_, ?_⟩
  · have h := hf e
    have hGe : G e = (2 : ZMod p) • e := by
      simp only [G, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, here]
      module
    rw [hGe] at h
    exact (smul_left_inj he0).mp h
  · intro v
    have h := hf v
    rw [h]
    simp only [G, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap]
    abel

private lemma cross_ne_zero_aux
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) {r s : V ≃ₗ[ZMod p] V} {xr xs : V} {fr fs : Module.Dual (ZMod p) V}
    (hfrx : fr xr = 2) (hfsx : fs xs = 2)
    (hTr : ∀ v, r v = v - fr v • xr) (hTs : ∀ v, s v = v - fs v • xs)
    (hnotr : ∀ g ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    (h0 : fr xs = 0) (hfsxr : fs xr ≠ 0) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  obtain ⟨hxr0, -⟩ := ne_zero_of_apply_eq_two hp2 hfrx
  obtain ⟨hxs0, -⟩ := ne_zero_of_apply_eq_two hp2 hfsx
  have hr_eq : r = Module.reflection hfrx :=
    LinearEquiv.ext fun v => by rw [hTr v, Module.reflection_apply]
  have hs_eq : s = Module.reflection hfsx :=
    LinearEquiv.ext fun v => by rw [hTs v, Module.reflection_apply]
  let g : V ≃ₗ[ZMod p] V := (r * s) ^ 2
  have hg_formula : ∀ z, g z = z + (fs xr * fr z) • xs := by
    intro z
    have h := reflection_mul_reflection_sq_apply_of_eq_zero hfrx hfsx h0 z
    rw [← hr_eq, ← hs_eq] at h
    simpa [g] using h
  have hg_ne : g ≠ 1 := by
    intro hg1
    have hgxr : g xr = xr := by rw [hg1]; rfl
    have hx := hg_formula xr
    rw [hfrx, hgxr] at hx
    have hsub : (fs xr * 2) • xs = 0 := by
      have := congrArg (fun w => w - xr) hx.symm
      simpa using this
    rcases smul_eq_zero.mp hsub with h | h
    · exact hfsxr ((mul_eq_zero.mp h).resolve_right h2)
    · exact hxs0 h
  have hg_mem : g ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)) := by
    have hr' : r ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)) :=
      Subgroup.subset_closure (by simp)
    have hs' : s ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)) :=
      Subgroup.subset_closure (by simp)
    have hrs : r * s ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)) :=
      Subgroup.mul_mem _ hr' hs'
    have h2' : (r * s) ^ 2 ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)) := by
      rw [pow_two]; exact Subgroup.mul_mem _ hrs hrs
    simpa [g] using h2'
  have hg_line : ggLinMove g = ZMod p ∙ xs := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ LinearMap.range (g.toLinearMap - LinearMap.id) := by
        simpa only [ggLinMove] using hy
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy'
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hg_formula z,
        add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self xs)
    · rw [Submodule.span_le]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hfsxr2 : fs xr * 2 ≠ 0 := mul_ne_zero hfsxr h2
      have hcoef : fs xr * ((fs xr * 2)⁻¹ * 2) = 1 := by
        calc fs xr * ((fs xr * 2)⁻¹ * 2)
            = (fs xr * 2) * (fs xr * 2)⁻¹ := by ring
          _ = 1 := mul_inv_cancel₀ hfsxr2
      refine LinearMap.mem_range.mpr ⟨((fs xr * 2)⁻¹) • xr, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hg_formula,
        add_sub_cancel_left, map_smul, hfrx, smul_eq_mul, hcoef, one_smul]
  have hfix : ggLinMove g ≤ ggLinFix {g} := by
    rw [hg_line]
    rw [Submodule.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    show ∀ a ∈ ({g} : Set (V ≃ₗ[ZMod p] V)), a xs = xs
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha, hg_formula xs, h0, mul_zero, zero_smul, add_zero]
  have hfin : Module.finrank (ZMod p) (ggLinMove g) = 1 := by
    rw [hg_line, finrank_span_singleton hxs0]
  exact hnotr g hg_mem hg_ne ⟨hfin, hfix⟩

theorem ggLin_adj_of_not_commute
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (r s : V ≃ₗ[ZMod p] V) (hr : GGLinRefl r) (hs : GGLinRefl s)
    (hnc : r * s ≠ s * r)
    (hnotr : ∀ g ∈ Subgroup.closure ({r, s} : Set (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g})) :
    GGLinAdj r s := by
  obtain ⟨xr, fr, hxr0, hspan_r, hfrx, hTr⟩ := exists_span_and_repr_of_ggLinRefl hr
  obtain ⟨xs, fs, hxs0, hspan_s, hfsx, hTs⟩ := exists_span_and_repr_of_ggLinRefl hs
  have hnotr_swap : ∀ g ∈ Subgroup.closure ({s, r} : Set (V ≃ₗ[ZMod p] V)), g ≠ 1 →
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}) := by
    intro g hg
    rw [Set.pair_comm s r] at hg
    exact hnotr g hg
  have hcomm_of_frxs_zero : fr xs = 0 → r * s = s * r := by
    intro h0
    have hfsxr0 : fs xr = 0 := by
      by_contra hfsxr
      exact cross_ne_zero_aux hp2 hfrx hfsx hTr hTs hnotr h0 hfsxr
    have hr_eq : r = Module.reflection hfrx :=
      LinearEquiv.ext fun v => by rw [hTr v, Module.reflection_apply]
    have hs_eq : s = Module.reflection hfsx :=
      LinearEquiv.ext fun v => by rw [hTs v, Module.reflection_apply]
    ext v
    rw [hr_eq, hs_eq, reflection_mul_reflection_apply' hfrx hfsx,
      reflection_mul_reflection_apply' hfsx hfrx, h0, hfsxr0]
    module
  have hfrxs : fr xs ≠ 0 := by
    intro h0
    exact hnc (hcomm_of_frxs_zero h0)
  have hfsxr : fs xr ≠ 0 := by
    intro h0
    have hfrxs0 : fr xs = 0 := by
      by_contra hfr
      exact cross_ne_zero_aux hp2 hfsx hfrx hTs hTr hnotr_swap h0 hfr
    exact hfrxs hfrxs0
  have hxr_mem : xr ∈ ggLinMove r := by
    rw [hspan_r]; exact Submodule.mem_span_singleton_self xr
  have hxs_mem : xs ∈ ggLinMove s := by
    rw [hspan_s]; exact Submodule.mem_span_singleton_self xs
  have hrxs : r xs ≠ xs := by
    intro h
    have hzero : fr xs • xr = 0 := by
      have h' := h
      rw [hTr xs] at h'
      have h'' := congrArg (fun w => w - xs) h'
      simpa using h''
    exact hfrxs ((smul_eq_zero.mp hzero).resolve_right hxr0)
  have hsxr : s xr ≠ xr := by
    intro h
    have hzero : fs xr • xs = 0 := by
      have h' := h
      rw [hTs xr] at h'
      have h'' := congrArg (fun w => w - xr) h'
      simpa using h''
    exact hfsxr ((smul_eq_zero.mp hzero).resolve_right hxs0)
  exact ⟨⟨xs, hxs_mem, hrxs⟩, ⟨xr, hxr_mem, hsxr⟩⟩

end CFSG.StandardType

end
