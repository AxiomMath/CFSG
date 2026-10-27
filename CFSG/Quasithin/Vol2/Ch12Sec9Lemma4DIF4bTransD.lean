module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bTransC
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelE
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bWitt

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin CFSG.Open

section Pt

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem mem_stab_span_iff_fix (γ : Model.VM ≃ₗ[ZMod 2] Model.VM) {w : Model.VM} (hw : w ≠ 0) :
    (∀ v, v ∈ Submodule.span (ZMod 2) {w} ↔ γ v ∈ Submodule.span (ZMod 2) {w}) ↔ γ w = w := by
  constructor
  · intro h
    have h1 : γ w ∈ Submodule.span (ZMod 2) {w} := (h w).1 (Submodule.mem_span_singleton_self w)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
    rcases zmod2_cases a with rfl | rfl
    · exfalso
      apply hw
      have : γ w = γ 0 := by rw [← ha, zero_smul, map_zero]
      exact γ.injective this
    · rw [one_smul] at ha
      exact ha.symm
  · intro hγw v
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hv
      rw [← ha, map_smul, hγw]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hv
      have hsymm : γ.symm w = w := by
        rw [LinearEquiv.symm_apply_eq]
        exact hγw.symm
      have hv' : a • w = v := by
        have := congrArg γ.symm ha
        rw [LinearEquiv.symm_apply_apply, map_smul, hsymm] at this
        exact this
      rw [← hv']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)

theorem e0_ne_zero : Model.e0 ≠ 0 := by decide

theorem stabS_span_conj_iff {w : W} (e : W ≃ₗ[ZMod 2] Model.VM)
    (hwe : ∀ v, v ∈ Submodule.span (ZMod 2) {w} ↔
      e v ∈ Submodule.span (ZMod 2) {Model.e0})
    (γ : W ≃ₗ[ZMod 2] W) :
    γ ∈ stabS (Submodule.span (ZMod 2) {w}) ↔
      conjEW e γ ∈ Model.stabM (Submodule.span (ZMod 2) {Model.e0}) := by
  show (∀ v, v ∈ Submodule.span (ZMod 2) {w} ↔ γ v ∈ Submodule.span (ZMod 2) {w}) ↔
    (∀ x, x ∈ Submodule.span (ZMod 2) {Model.e0} ↔
      conjEW e γ x ∈ Submodule.span (ZMod 2) {Model.e0})
  constructor
  · intro h x
    have h1 := hwe (e.symm x)
    rw [e.apply_symm_apply] at h1
    have h2 := hwe (γ (e.symm x))
    rw [conjE_apply, ← h1, ← h2]
    exact h (e.symm x)
  · intro h v
    rw [hwe v, hwe (γ v)]
    have := h (e v)
    rw [conjE_apply, e.symm_apply_apply] at this
    exact this

theorem stabS_span_map_eq {w : W} (e : W ≃ₗ[ZMod 2] Model.VM)
    (hwe : ∀ v, v ∈ Submodule.span (ZMod 2) {w} ↔
      e v ∈ Submodule.span (ZMod 2) {Model.e0}) :
    (stabS (Submodule.span (ZMod 2) {w})).map
        (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) =
      Model.stabM (Submodule.span (ZMod 2) {Model.e0}) := by
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact (stabS_span_conj_iff e hwe γ).1 hγ
  · intro hδ
    exact ⟨(conjEW e).symm δ, (stabS_span_conj_iff e hwe _).2
      (by rw [MulEquiv.apply_symm_apply]; exact hδ), MulEquiv.apply_symm_apply _ _⟩

theorem stab_span_e0_inf (Ω' : Subgroup (Model.VM ≃ₗ[ZMod 2] Model.VM)) (hΩ' : Ω' ≤ Model.GM) :
    Model.stabM (Submodule.span (ZMod 2) {Model.e0}) ⊓ Ω' = Model.Hm ⊓ Ω' := by
  ext δ
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    have hfix : δ Model.e0 = Model.e0 :=
      (mem_stab_span_iff_fix δ e0_ne_zero).1 ((Model.mem_stabM_iff _ _).1 h1)
    exact Subgroup.mem_inf.2 ⟨(Model.mem_Hm_iff δ).2 ⟨hΩ' h2, hfix⟩, h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 h
    have hfix : δ Model.e0 = Model.e0 := ((Model.mem_Hm_iff δ).1 h1).2
    exact Subgroup.mem_inf.2 ⟨(Model.mem_stabM_iff _ _).2
      ((mem_stab_span_iff_fix δ e0_ne_zero).2 hfix), h2⟩

end Pt

section Frame

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_frame_of_singular [Finite W] (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0)
    (hdim : Module.finrank (ZMod 2) W = 6)
    (hS : ∃ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = 3 ∧ ∀ s ∈ S, q s = 0)
    {w : W} (hw : w ≠ 0) (hqw : q w = 0) :
    ∃ e : W ≃ₗ[ZMod 2] Model.VM, (∀ v, Model.qM (e v) = q v) ∧ e w = Model.e0 := by
  haveI : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨S, hS3, hSs⟩ := hS
  obtain ⟨b, hb1, _hb2, _hb3, hb5, _hbS⟩ :=
    exists_witt_basis_of_MTS q B hq hB hdim S hS3 hSs
  have hb1' : q (b (Sum.inl 0)) = 0 := (hb1 0).1
  have hbne : b (Sum.inl 0) ≠ 0 := b.ne_zero _
  obtain ⟨γ0, hγ0, hγ0b⟩ := singular_transitive q B hq hB hbne hw hb1' hqw
  have hqγ : ∀ v, q (γ0 v) = q v := fun v => hγ0 v
  have he_b : ∀ x, Model.qM (b.equivFun x) = q x := by
    intro x
    have hv : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    rw [Fintype.sum_sum_type] at hv
    have key : q x = ∑ i, b.repr x (.inl i) * b.repr x (.inr i) := by
      conv_lhs => rw [hv]
      exact hb5 (fun i => b.repr x (.inl i)) (fun i => b.repr x (.inr i))
    rw [key]
    simp only [Model.qM, Model.xp, Model.yp, dotProduct, Module.Basis.equivFun_apply]
  let e : W ≃ₗ[ZMod 2] Model.VM := (γ0.symm).trans b.equivFun
  refine ⟨e, ?_, ?_⟩
  · intro v
    show Model.qM (b.equivFun (γ0.symm v)) = q v
    rw [he_b]
    have h := hqγ (γ0.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · show b.equivFun (γ0.symm w) = Model.e0
    have hs : γ0.symm w = b (Sum.inl 0) := by
      rw [LinearEquiv.symm_apply_eq]
      exact hγ0b.symm
    rw [hs]
    funext j
    rw [Module.Basis.equivFun_self]
    revert j
    decide

theorem part_d_of_frame [Finite W] (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (Ω : Subgroup (W ≃ₗ[ZMod 2] W)) (hΩ : Ω ≤ orthogonalSubgroupOf q)
    (hrel : Ω.relIndex (orthogonalSubgroupOf q) = 2)
    {w : W} (hw : w ≠ 0) (e : W ≃ₗ[ZMod 2] Model.VM) (he : ∀ v, Model.qM (e v) = q v)
    (hew : e w = Model.e0) :
    Nat.card (pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω)) = 16 ∧
    ∀ γ ∈ stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω,
      (∀ x : W, B x w = 0 → γ x - x ∈ Submodule.span (ZMod 2) {w}) ↔
        γ ∈ pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω) := by
  have hwe : ∀ v, v ∈ Submodule.span (ZMod 2) {w} ↔
      e v ∈ Submodule.span (ZMod 2) {Model.e0} := by
    intro v
    rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [map_smul, hew]⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, e.injective ?_⟩
      rw [map_smul, hew, ha]
  have hBe : ∀ x y : W, B x y = Model.bM (e x) (e y) := by
    intro x y
    have h1 := hq x y
    have h2 : q (x + y) = q x + q y + Model.bM (e x) (e y) := by
      rw [← he (x + y), ← he x, ← he y, map_add, Model.qM_add]
    linear_combination h2 - h1
  have hGM := GM_map_eq q e he
  have hΩG : Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) ≤ Model.GM := by
    rw [← hGM]
    exact Subgroup.map_mono hΩ
  have hrelM : (Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))).relIndex
      Model.GM = 2 := by
    rw [← hGM, Subgroup.relIndex_map_map_of_injective
      (f := (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))) _ _ (conjEW e).injective,
      hrel]
  obtain ⟨hcard, hker⟩ := Model.model_w_claims hΩG hrelM
  have hmap : (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω).map
      (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) =
      Model.Hm ⊓ Ω.map (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) := by
    rw [Subgroup.map_inf _ _ (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))
      (conjEW e).injective, stabS_span_map_eq e hwe, stab_span_e0_inf _ hΩG]
  have hcardW : Nat.card (pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω)) = 16 := by
    have h := CFSG.Quasithin.F112R.card_pCoreOf_of_mulEquiv
      (MulEquiv.subgroupMap (conjEW e) (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω)) 2
    rw [hmap] at h
    rw [h, hcard]
  refine ⟨hcardW, ?_⟩
  intro γ hγ
  have hδ : conjEW e γ ∈ Model.Hm ⊓ Ω.map
      (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM)) := by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨γ, hγ, rfl⟩
  have hmemiff := CFSG.Quasithin.F112R.mem_pCoreOf_iff_of_mulEquiv
    (MulEquiv.subgroupMap (conjEW e) (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω)) 2 ⟨γ, hγ⟩
  have hmem' : γ ∈ pCoreOf 2 (stabS (Submodule.span (ZMod 2) {w}) ⊓ Ω) ↔
      conjEW e γ ∈ pCoreOf 2 (Model.Hm ⊓ Ω.map
        (conjEW e : (W ≃ₗ[ZMod 2] W) →* (Model.VM ≃ₗ[ZMod 2] Model.VM))) := by
    rw [← hmap]
    exact hmemiff
  rw [hmem']
  have key : (∀ x : W, B x w = 0 → γ x - x ∈ Submodule.span (ZMod 2) {w}) ↔
      (∀ y : Model.VM, Model.bM y Model.e0 = 0 →
        conjEW e γ y - y ∈ Submodule.span (ZMod 2) {Model.e0}) := by
    constructor
    · intro h y hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : B x w = 0 := by
        rw [hBe x w, hew]
        exact hy
      have h1 := (hwe (γ x - x)).1 (h x hx)
      rw [map_sub] at h1
      rw [conjE_apply, e.symm_apply_apply]
      exact h1
    · intro h x hx
      have hy : Model.bM (e x) Model.e0 = 0 := by
        rw [← hew, ← hBe]
        exact hx
      have h1 := h (e x) hy
      rw [conjE_apply, e.symm_apply_apply] at h1
      apply (hwe (γ x - x)).2
      rw [map_sub]
      exact h1
  rw [key]
  exact hker (conjEW e γ) hδ

end Frame

end CFSG.Quasithin.H13.C1294

end
