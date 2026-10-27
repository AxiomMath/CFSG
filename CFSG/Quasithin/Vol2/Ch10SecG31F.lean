module

public import CFSG.Quasithin.Vol2.Ch10SecG31E

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def resF (U : Submodule (ZMod 2) W) (F : W → Submodule (ZMod 2) (Dual (ZMod 2) W))
    (u : U) : Submodule (ZMod 2) (Dual (ZMod 2) U) :=
  (F (u : W)).map U.subtype.dualMap

theorem mem_resF {U : Submodule (ZMod 2) W} {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}
    {u : U} {ψ : Dual (ZMod 2) U} : ψ ∈ resF U F u ↔ ∃ φ ∈ F (u : W), ∀ v : U, ψ v = φ v := by
  rw [resF, Submodule.mem_map]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, hφ, fun v => rfl⟩
  · rintro ⟨φ, hφ, h⟩
    exact ⟨φ, hφ, LinearMap.ext fun v => (h v).symm⟩

namespace Hyp

variable {Gm : Subgroup (W ≃ₗ[ZMod 2] W)} {Δ₀ : Set W}
  {F : W → Submodule (ZMod 2) (Dual (ZMod 2) W)}

theorem closure_gens_le (hH : Hyp Gm Δ₀ F) {Δ' : Set W} (hΔ' : Δ' ⊆ Δ₀) :
    Subgroup.closure (gens Δ' F) ≤ Gm :=
  (Subgroup.closure_le Gm).2 (by rintro t ⟨x, hx, φ, hφ, h, rfl⟩; exact hH.mem x (hΔ' hx) φ hφ h)

theorem exists_res {Δ' : Set W} {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ Subgroup.closure (gens Δ' F)) :
    ∃ g'' ∈ Subgroup.closure (gens (((↑) : Submodule.span (ZMod 2) Δ' → W) ⁻¹' Δ')
      (resF (Submodule.span (ZMod 2) Δ') F)),
      ∀ u : Submodule.span (ZMod 2) Δ', (g'' u : W) = g u := by
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨x, hx, φ, hφ, h, rfl⟩ := ht
    have hxU : x ∈ Submodule.span (ZMod 2) Δ' := Submodule.subset_span hx
    have h' : (Submodule.span (ZMod 2) Δ').subtype.dualMap φ ⟨x, hxU⟩ = 0 := h
    refine ⟨LinearEquiv.transvection h', Subgroup.subset_closure ⟨⟨x, hxU⟩, hx, _,
      Submodule.mem_map_of_mem hφ, h', rfl⟩, fun u => ?_⟩
    rw [transvection_apply, transvection_apply]
    rfl
  | one => exact ⟨1, Subgroup.one_mem _, fun u => rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a'', ha'', ha⟩ := ha
    obtain ⟨b'', hb'', hb⟩ := hb
    refine ⟨a'' * b'', Subgroup.mul_mem _ ha'' hb'', fun u => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
  | inv a _ ha =>
    obtain ⟨a'', ha'', ha⟩ := ha
    refine ⟨a''⁻¹, Subgroup.inv_mem _ ha'', fun u => ?_⟩
    show ((a''.symm u : Submodule.span (ZMod 2) Δ') : W) = a.symm u
    rw [eq_comm, LinearEquiv.symm_apply_eq, ← ha, LinearEquiv.apply_symm_apply]

theorem exists_lift (hH : Hyp Gm Δ₀ F) {Δ' : Set W} (hΔ' : Δ' ⊆ Δ₀)
    {g'' : Submodule.span (ZMod 2) Δ' ≃ₗ[ZMod 2] Submodule.span (ZMod 2) Δ'}
    (hg'' : g'' ∈ Subgroup.closure (gens (((↑) : Submodule.span (ZMod 2) Δ' → W) ⁻¹' Δ')
      (resF (Submodule.span (ZMod 2) Δ') F))) :
    ∃ g ∈ Subgroup.closure (gens Δ' F), ∀ u : Submodule.span (ZMod 2) Δ', (g'' u : W) = g u := by
  induction hg'' using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨x, hx, ψ, hψ, h, rfl⟩ := ht
    obtain ⟨φ, hφ, hψφ⟩ := mem_resF.1 hψ
    have hφx : φ x = 0 := hH.apply_self x (hΔ' hx) φ hφ
    refine ⟨LinearEquiv.transvection hφx, Subgroup.subset_closure ⟨x, hx, φ, hφ, hφx, rfl⟩,
      fun u => ?_⟩
    rw [transvection_apply, transvection_apply, hψφ]
    rfl
  | one => exact ⟨1, Subgroup.one_mem _, fun u => rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', ha⟩ := ha
    obtain ⟨b', hb', hb⟩ := hb
    refine ⟨a' * b', Subgroup.mul_mem _ ha' hb', fun u => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
  | inv a _ ha =>
    obtain ⟨a', ha', ha⟩ := ha
    refine ⟨a'⁻¹, Subgroup.inv_mem _ ha', fun u => ?_⟩
    show ((a.symm u : Submodule.span (ZMod 2) Δ') : W) = a'.symm u
    rw [eq_comm, LinearEquiv.symm_apply_eq, ← ha, LinearEquiv.apply_symm_apply]

variable [Finite W]

theorem invariant_span {Δ' : Set W} :
    G11.Invariant (Subgroup.closure (gens Δ' F)) (Submodule.span (ZMod 2) Δ') := by
  refine invariant_closure ?_
  rintro t ⟨x, hx, φ, -, h, rfl⟩ u hu
  rw [transvection_apply]
  exact Submodule.add_mem _ hu (Submodule.smul_mem _ _ (Submodule.subset_span hx))

theorem core_restrict (hH : Hyp Gm Δ₀ F) {Δ' : Set W} (hΔ' : Δ' ⊆ Δ₀)
    (hinv : ∀ g ∈ Subgroup.closure (gens Δ' F), ∀ x ∈ Δ', g x ∈ Δ')
    (htrans : ∀ x ∈ Δ', ∀ y ∈ Δ', ∃ g ∈ Subgroup.closure (gens Δ' F), g x = y)
    (hrank : ∀ x ∈ Δ', 2 ≤ finrank (ZMod 2) (F x))
    (hO2 : ∀ g ∈ Subgroup.closure (gens Δ' F), (∀ v ∈ Submodule.span (ZMod 2) Δ',
      ∀ h ∈ Subgroup.closure (gens Δ' F), h (g v - v) = g v - v) → g = 1) :
    (∀ v ∈ Submodule.span (ZMod 2) Δ', v ≠ 0 → v ∈ Δ') ∧
    (∀ g : Submodule.span (ZMod 2) Δ' ≃ₗ[ZMod 2] Submodule.span (ZMod 2) Δ',
      ∃ k ∈ Subgroup.closure (gens Δ' F), ∀ v : Submodule.span (ZMod 2) Δ', k v = g v) ∧
    (∀ x ∈ Δ', finrank (ZMod 2) (F x) + 1 =
      finrank (ZMod 2) (Submodule.span (ZMod 2) Δ')) := by
  set U := Submodule.span (ZMod 2) Δ' with hU
  have hG'm : Subgroup.closure (gens Δ' F) ≤ Gm := hH.closure_gens_le hΔ'
  have hinj : ∀ x ∈ Δ', ∀ φ ∈ F x, (∀ u ∈ U, φ u = 0) → φ = 0 := by
    intro x hx φ hφ hφU
    have hφx : φ x = 0 := hH.apply_self x (hΔ' hx) φ hφ
    have ht := hO2 _ (Subgroup.subset_closure ⟨x, hx, φ, hφ, hφx, rfl⟩) fun v hv h _ => by
      rw [transvection_apply, add_sub_cancel_left, hφU v hv, zero_smul, map_zero]
    refine LinearMap.ext fun w => ?_
    have h1 := congrArg (fun g : W ≃ₗ[ZMod 2] W => g w) ht
    change w + φ w • x = w at h1
    rw [add_eq_left] at h1
    rcases zmod_two_eq_zero_or_one (φ w) with h0 | h0
    · exact h0
    · rw [h0, one_smul] at h1
      exact absurd h1 (hH.ne_zero x (hΔ' hx))
  have hH'' : Hyp (Subgroup.closure (gens (((↑) : U → W) ⁻¹' Δ') (resF U F)))
      (((↑) : U → W) ⁻¹' Δ') (resF U F) := by
    refine ⟨fun x hx h0 => hH.ne_zero _ (hΔ' hx) (by simp [h0]), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx ψ hψ
      obtain ⟨φ, hφ, hψφ⟩ := mem_resF.1 hψ
      rw [hψφ]
      exact hH.apply_self _ (hΔ' hx) φ hφ
    · intro x hx ψ hψ h
      exact Subgroup.subset_closure ⟨x, hx, ψ, hψ, h, rfl⟩
    · intro g'' hg'' x hx
      obtain ⟨g, hg, hgg⟩ := hH.exists_lift hΔ' hg''
      show ((g'' x : U) : W) ∈ Δ'
      rw [hgg]
      exact hinv g hg x hx
    · intro g'' hg'' x hx ψ
      obtain ⟨g, hg, hgg⟩ := hH.exists_lift hΔ' hg''
      rw [mem_resF, mem_resF, hgg x]
      constructor
      · rintro ⟨φ, hφ, hψφ⟩
        refine ⟨φ ∘ₗ (g : W →ₗ[ZMod 2] W),
          (hH.mem_F_map g (hG'm hg) x (hΔ' hx) φ).1 hφ, fun v => ?_⟩
        show ψ (g'' v) = φ (g v)
        rw [hψφ, hgg]
      · rintro ⟨φ', hφ', hψφ'⟩
        refine ⟨φ' ∘ₗ (g.symm : W →ₗ[ZMod 2] W),
          (hH.mem_F_map g (hG'm hg) x (hΔ' hx) _).2 ?_, fun v => ?_⟩
        · convert hφ' using 1
          ext w
          simp
        · have hw : (v : W) = g ((g''.symm v : U) : W) := by
            rw [← hgg, LinearEquiv.apply_symm_apply]
          have h1 := hψφ' (g''.symm v)
          rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
          rw [h1]
          show φ' ((g''.symm v : U) : W) = φ' (g.symm (v : W))
          rw [hw, LinearEquiv.symm_apply_apply]
    · intro x hx y hy
      obtain ⟨g, hg, hgxy⟩ := htrans x hx y hy
      obtain ⟨g'', hg'', hgg⟩ := exists_res hg
      exact ⟨g'', hg'', Subtype.ext (by rw [hgg, hgxy])⟩
  have hfr : ∀ x : U, (x : W) ∈ Δ' →
      finrank (ZMod 2) (resF U F x) = finrank (ZMod 2) (F (x : W)) := by
    intro x hx
    have hinj' : Function.Injective ((U.subtype.dualMap).domRestrict (F (x : W))) := by
      refine (injective_iff_map_eq_zero _).2 fun φ hφ =>
        Subtype.ext (hinj x hx φ φ.2 fun u hu => ?_)
      exact LinearMap.congr_fun hφ ⟨u, hu⟩
    rw [(LinearEquiv.ofInjective _ hinj').finrank_eq, LinearMap.range_domRestrict]
    rfl
  have hO2'' : ∀ g'' ∈ Subgroup.closure (gens (((↑) : U → W) ⁻¹' Δ') (resF U F)),
      (∀ w, ∀ h'' ∈ Subgroup.closure (gens (((↑) : U → W) ⁻¹' Δ') (resF U F)),
        h'' (g'' w - w) = g'' w - w) → g'' = 1 := by
    intro g'' hg'' hfix
    obtain ⟨g, hg, hgg⟩ := hH.exists_lift hΔ' hg''
    have h1 := hO2 g hg fun v hv h hh => by
      obtain ⟨h'', hh'', hhh⟩ := exists_res hh
      have e : g v - v = ((g'' ⟨v, hv⟩ - ⟨v, hv⟩ : U) : W) := by
        rw [Submodule.coe_sub, hgg]
      rw [e, ← hhh, hfix ⟨v, hv⟩ h'' hh'']
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [hgg, h1]
    rfl
  obtain ⟨h1, h2, h3⟩ := hH''.core le_rfl Submodule.span_span_coe_preimage
    (fun x hx => (hfr x hx).symm ▸ hrank _ hx) hO2''
  refine ⟨fun v hv hv0 => h1 ⟨v, hv⟩ fun h => hv0 (congrArg Subtype.val h), fun g => ?_,
    fun x hx => ?_⟩
  · obtain ⟨k, hk, hkg⟩ := hH.exists_lift hΔ' (g'' := g) (by rw [h3]; trivial)
    exact ⟨k, hk, fun v => (hkg v).symm⟩
  · have hxU : x ∈ U := Submodule.subset_span hx
    have hx0 : (⟨x, hxU⟩ : U) ≠ 0 := fun h => hH.ne_zero x (hΔ' hx) (congrArg Subtype.val h)
    have h4 := Subspace.finrank_add_finrank_dualAnnihilator_eq
      (Submodule.span (ZMod 2) {(⟨x, hxU⟩ : U)})
    rw [← h2 ⟨x, hxU⟩ hx, finrank_span_singleton hx0, hfr ⟨x, hxU⟩ hx] at h4
    change 1 + finrank (ZMod 2) (F x) = finrank (ZMod 2) U at h4
    omega

end Hyp

end CFSG.Quasithin.G31
