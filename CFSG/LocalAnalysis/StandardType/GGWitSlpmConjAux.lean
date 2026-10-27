module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

theorem wSlpmC_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : Nat.Prime p := Fact.out
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

theorem wSlpmC_ne_zero {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {a : U} {α : U →ₗ[ZMod p] ZMod p} (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) : a ≠ 0 := by
  intro ha
  rw [ha, map_zero] at hα
  exact h2 hα.symm

theorem wSlpmC_isCompl {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) : IsCompl (ZMod p ∙ a) (LinearMap.ker α) := by
  refine IsCompl.mk ?_ ?_
  · refine ((Submodule.disjoint_span_singleton (s := LinearMap.ker α) (x := a)).mpr ?_).symm
    intro ha
    have h0 : (2 : ZMod p) = 0 := by rw [← hα, LinearMap.mem_ker.mp ha]
    exact absurd h0 h2
  · rw [codisjoint_iff]
    rw [LinearMap.span_singleton_sup_ker_eq_top α (by rw [hα]; exact h2)]

noncomputable def wSlpmC_Ea {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) :
    (↥(ZMod p ∙ a) × ↥(LinearMap.ker α)) ≃ₗ[ZMod p] U :=
  (ZMod p ∙ a).prodEquivOfIsCompl (LinearMap.ker α) (wSlpmC_isCompl a α hα h2)

theorem wSlpmC_Ea_apply {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) (x : ↥(ZMod p ∙ a)) (y : ↥(LinearMap.ker α)) :
    wSlpmC_Ea a α hα h2 (x, y) = (x : U) + (y : U) := by
  simp [wSlpmC_Ea, Submodule.coe_prodEquivOfIsCompl, LinearMap.coprod_apply,
    Submodule.subtype_apply]

theorem wSlpmC_finrank_ker {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p)
    (hα : α a = 2) (h2 : (2 : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) ↥(LinearMap.ker α) = Module.finrank (ZMod p) U - 1 := by
  have he : Module.finrank (ZMod p) (↥(ZMod p ∙ a) × ↥(LinearMap.ker α)) =
      Module.finrank (ZMod p) U := (wSlpmC_Ea a α hα h2).finrank_eq
  rw [Module.finrank_prod, finrank_span_singleton (wSlpmC_ne_zero hα h2)] at he
  omega

noncomputable def wSlpmC_spanEquiv {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a b : U) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ZMod p ∙ a) ≃ₗ[ZMod p] (ZMod p ∙ b) :=
  (LinearEquiv.toSpanNonzeroSingleton (ZMod p) U a ha).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod p) U b hb)

noncomputable def wSlpmC_glue {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) (b : U) (β : U →ₗ[ZMod p] ZMod p) (hβ : β b = 2)
    (e : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker β)) : U ≃ₗ[ZMod p] U :=
  (wSlpmC_Ea a α hα h2).symm.trans
    (((wSlpmC_spanEquiv a b (wSlpmC_ne_zero hα h2) (wSlpmC_ne_zero hβ h2)).prodCongr e).trans
      (wSlpmC_Ea b β hβ h2))

theorem wSlpmC_glue_apply {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) (b : U) (β : U →ₗ[ZMod p] ZMod p) (hβ : β b = 2)
    (e : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker β))
    (x : ↥(ZMod p ∙ a)) (y : ↥(LinearMap.ker α)) :
    wSlpmC_glue a α hα h2 b β hβ e (wSlpmC_Ea a α hα h2 (x, y)) =
      wSlpmC_Ea b β hβ h2
        ((wSlpmC_spanEquiv a b (wSlpmC_ne_zero hα h2) (wSlpmC_ne_zero hβ h2)) x, e y) := by
  simp only [wSlpmC_glue, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.symm_apply_apply]

theorem wSlpmC_of_refl_a {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {a : U} {α : U →ₗ[ZMod p] ZMod p} (hα : α a = 2)
    (r : U ≃ₗ[ZMod p] U) (hr : ∀ v, r v = v - α v • a) : r a = -a := by
  rw [hr, hα, two_smul]
  abel

theorem wSlpmC_of_refl_ker {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {a : U} {α : U →ₗ[ZMod p] ZMod p}
    (r : U ≃ₗ[ZMod p] U) (hr : ∀ v, r v = v - α v • a) (y : ↥(LinearMap.ker α)) :
    r (y : U) = (y : U) := by
  rw [hr, LinearMap.mem_ker.mp y.2, zero_smul, sub_zero]

theorem wSlpmC_of_refl_span {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {a : U} {α : U →ₗ[ZMod p] ZMod p} (hα : α a = 2)
    (r : U ≃ₗ[ZMod p] U) (hr : ∀ v, r v = v - α v • a)
    (x : ↥(ZMod p ∙ a)) : r (x : U) = -(x : U) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
  rw [← hc, LinearEquiv.map_smul, wSlpmC_of_refl_a hα r hr, smul_neg]

theorem wSlpmC_of_refl_Ea {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {a : U} {α : U →ₗ[ZMod p] ZMod p} (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0) (r : U ≃ₗ[ZMod p] U) (hr : ∀ v, r v = v - α v • a)
    (x : ↥(ZMod p ∙ a)) (y : ↥(LinearMap.ker α)) :
    r (wSlpmC_Ea a α hα h2 (x, y)) = wSlpmC_Ea a α hα h2 (-x, y) := by
  rw [wSlpmC_Ea_apply, wSlpmC_Ea_apply, map_add, wSlpmC_of_refl_span hα r hr,
    wSlpmC_of_refl_ker r hr, Submodule.coe_neg]

theorem wSlpmC_glue_conj_of {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a b : U) (α β : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (hβ : β b = 2) (h2 : (2 : ZMod p) ≠ 0) (r s : U ≃ₗ[ZMod p] U)
    (hr : ∀ v, r v = v - α v • a) (hs : ∀ v, s v = v - β v • b)
    (e : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker β)) :
    wSlpmC_glue a α hα h2 b β hβ e * r * (wSlpmC_glue a α hα h2 b β hβ e)⁻¹ = s := by
  have h : wSlpmC_glue a α hα h2 b β hβ e * r =
      s * wSlpmC_glue a α hα h2 b β hβ e := by
    ext z
    rcases (wSlpmC_Ea a α hα h2).surjective z with ⟨⟨x, y⟩, rfl⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, wSlpmC_of_refl_Ea hα h2 r hr,
      wSlpmC_glue_apply, wSlpmC_glue_apply, wSlpmC_of_refl_Ea hβ h2 s hs, map_neg]
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

noncomputable def wSlpmC_block {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0)
    (φ : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker α)) : U ≃ₗ[ZMod p] U :=
  ((wSlpmC_Ea a α hα h2).symm.trans
    ((LinearEquiv.refl (ZMod p) (↥(ZMod p ∙ a))).prodCongr φ)).trans
    (wSlpmC_Ea a α hα h2)

theorem wSlpmC_block_apply {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (h2 : (2 : ZMod p) ≠ 0)
    (φ : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker α))
    (x : ↥(ZMod p ∙ a)) (y : ↥(LinearMap.ker α)) :
    wSlpmC_block a α hα h2 φ (wSlpmC_Ea a α hα h2 (x, y)) =
      wSlpmC_Ea a α hα h2 (x, φ y) := by
  simp only [wSlpmC_block, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply]

theorem wSlpmC_glue_mul_block {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (a b : U) (α β : U →ₗ[ZMod p] ZMod p) (hα : α a = 2)
    (hβ : β b = 2) (h2 : (2 : ZMod p) ≠ 0)
    (e : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker β))
    (φ : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker α)) :
    wSlpmC_glue a α hα h2 b β hβ (φ.trans e) =
      wSlpmC_glue a α hα h2 b β hβ e * wSlpmC_block a α hα h2 φ := by
  ext z
  rcases (wSlpmC_Ea a α hα h2).surjective z with ⟨⟨x, y⟩, rfl⟩
  simp only [wSlpmC_glue_apply, wSlpmC_block_apply, LinearEquiv.mul_apply,
    LinearEquiv.trans_apply]

theorem wSlpmC_det_prodCongr {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [Module.Free R M] [Module.Free R M']
    [Module.Finite R M] [Module.Finite R M'] (e₁ : M ≃ₗ[R] M) (e₂ : M' ≃ₗ[R] M') :
    LinearEquiv.det (e₁.prodCongr e₂) = LinearEquiv.det e₁ * LinearEquiv.det e₂ := by
  ext
  simp only [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap,
    Units.val_mul]

theorem wSlpmC_det_smulOfUnit_span {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (w : V) (hw : w ≠ 0) (u : (ZMod p)ˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit u : (ZMod p ∙ w) ≃ₗ[ZMod p] (ZMod p ∙ w)) = u := by
  ext
  rw [LinearEquiv.coe_det]
  have hco : (LinearEquiv.smulOfUnit u : ↥(ZMod p ∙ w) ≃ₗ[ZMod p] ↥(ZMod p ∙ w)).toLinearMap =
      (u : ZMod p) • (1 : ↥(ZMod p ∙ w) →ₗ[ZMod p] ↥(ZMod p ∙ w)) := by
    ext x : 1
    change (u • x : ↥(ZMod p ∙ w)) = (u : ZMod p) • x
    rw [Units.smul_def]
  rw [hco, LinearMap.det_smul, map_one, mul_one, finrank_span_singleton hw, pow_one]

theorem wSlpmC_block_det {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p)
    (hα : α a = 2) (h2 : (2 : ZMod p) ≠ 0)
    (φ : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker α)) :
    LinearEquiv.det (wSlpmC_block a α hα h2 φ) = LinearEquiv.det φ := by
  rw [wSlpmC_block, LinearEquiv.det_conj, wSlpmC_det_prodCongr, LinearEquiv.det_refl, one_mul]

theorem wSlpmC_exists_aut_det {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (a : U) (α : U →ₗ[ZMod p] ZMod p)
    (hα : α a = 2) (h2 : (2 : ZMod p) ≠ 0) (hd : 3 ≤ Module.finrank (ZMod p) U)
    (u : (ZMod p)ˣ) :
    ∃ φ : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker α), LinearEquiv.det φ = u := by
  have hker := wSlpmC_finrank_ker a α hα h2
  have hne : LinearMap.ker α ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker
    omega
  obtain ⟨w, hwV, hw0⟩ := (Submodule.ne_bot_iff (LinearMap.ker α)).mp hne
  let wL : ↥(LinearMap.ker α) := ⟨w, hwV⟩
  have hwL0 : wL ≠ 0 := by
    intro h
    exact hw0 (by simpa [wL] using congrArg (fun x : ↥(LinearMap.ker α) => (x : U)) h)
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (ZMod p ∙ wL)
  let D : (↥(ZMod p ∙ wL) × ↥W) ≃ₗ[ZMod p] ↥(LinearMap.ker α) :=
    (ZMod p ∙ wL).prodEquivOfIsCompl W hW
  let f : (↥(ZMod p ∙ wL) × ↥W) ≃ₗ[ZMod p] (↥(ZMod p ∙ wL) × ↥W) :=
    (LinearEquiv.smulOfUnit u : ↥(ZMod p ∙ wL) ≃ₗ[ZMod p] ↥(ZMod p ∙ wL)).prodCongr
      (LinearEquiv.refl (ZMod p) ↥W)
  refine ⟨(D.symm.trans f).trans D, ?_⟩
  rw [LinearEquiv.det_conj, wSlpmC_det_prodCongr, wSlpmC_det_smulOfUnit_span wL hwL0 u,
    LinearEquiv.det_refl, mul_one]

theorem wSlpmC_isRefl_form {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [Module.Finite (ZMod p) U] (h2 : (2 : ZMod p) ≠ 0)
    (t : U ≃ₗ[ZMod p] U) (ht : IsRefl p t) :
    ∃ (a : U) (α : U →ₗ[ZMod p] ZMod p) (hα : α a = 2), ∀ v, t v = v - α v • a := by
  let τ : U →ₗ[ZMod p] U := t.toLinearMap - LinearMap.id
  have hτfin : Module.finrank (ZMod p) ↥(LinearMap.range τ) = 1 := ht.2
  have hne : LinearMap.range τ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hτfin
    omega
  obtain ⟨a, ha_mem, ha0⟩ := (Submodule.ne_bot_iff (LinearMap.range τ)).mp hne
  have hττ : ∀ v, τ (τ v) = -((2 : ZMod p) • τ v) := by
    intro v
    have h1 : t.toLinearMap (t.toLinearMap v) = v := by
      have := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) ht.1
      simpa [LinearEquiv.mul_apply] using this
    simp only [τ, LinearMap.sub_apply, LinearMap.id_apply, map_sub, h1]
    rw [two_smul]
    abel
  have hτa : τ a = -((2 : ZMod p) • a) := by
    obtain ⟨v, rfl⟩ := ha_mem
    exact hττ v
  have hspan_le : (ZMod p ∙ a) ≤ LinearMap.range τ :=
    Submodule.span_le.mpr (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact ha_mem)
  have hspan_eq : (ZMod p ∙ a) = LinearMap.range τ :=
    Submodule.eq_of_le_of_finrank_eq hspan_le
      (by rw [finrank_span_singleton ha0, hτfin])
  let σ : ZMod p →ₗ[ZMod p] U := LinearMap.toSpanSingleton (ZMod p) U a
  have hσinj : Function.Injective σ := by
    intro x y hxy
    have h0 : x • a = y • a := by simpa [σ, LinearMap.toSpanSingleton] using hxy
    have h1 : (x - y) • a = 0 := by rw [sub_smul, h0, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right ha0)
  let eσ : ZMod p ≃ₗ[ZMod p] ↥(LinearMap.range σ) := LinearEquiv.ofInjective σ hσinj
  have hσrange : LinearMap.range σ = ZMod p ∙ a := by
    change (LinearMap.toSpanSingleton (ZMod p) U a).range = ZMod p ∙ a
    rw [LinearMap.range_toSpanSingleton]
  let τ₂ : U →ₗ[ZMod p] U := (0 : U →ₗ[ZMod p] U) - τ
  have hτ₂ : ∀ v, τ₂ v = -τ v := by
    intro v
    simp only [τ₂, LinearMap.sub_apply, LinearMap.zero_apply, zero_sub,
      LinearMap.neg_apply]
  let τ' : U →ₗ[ZMod p] ↥(LinearMap.range σ) :=
    τ₂.codRestrict (LinearMap.range σ) (fun v => by
      have hv : τ v ∈ LinearMap.range τ := LinearMap.mem_range.mpr ⟨v, rfl⟩
      rw [← hspan_eq] at hv
      rw [hσrange, hτ₂ v]
      exact Submodule.neg_mem _ hv)
  let γ : U →ₗ[ZMod p] ZMod p := eσ.symm.toLinearMap.comp τ'
  have hσγ : ∀ v, σ (γ v) = -τ v := by
    intro v
    have h1 : eσ (γ v) = τ' v := by
      simp only [γ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      exact LinearEquiv.apply_symm_apply eσ (τ' v)
    have h2' := congrArg (fun x : ↥(LinearMap.range σ) => (x : U)) h1
    have h3 : σ (γ v) = τ₂ v := by
      simpa [eσ, τ', LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] using h2'
    rw [h3, hτ₂ v]
  have hγa : γ a = 2 := by
    have h1 : σ (γ a) = σ (2 : ZMod p) := by
      rw [hσγ, hτa]
      show -(-((2 : ZMod p) • a)) = σ (2 : ZMod p)
      change -(-((2 : ZMod p) • a)) = (2 : ZMod p) • a
      rw [neg_neg]
    exact hσinj h1
  refine ⟨a, γ, hγa, ?_⟩
  · intro v
    have hτv : τ v = -(γ v • a) := by
      have h := hσγ v
      have h2 : σ (γ v) = γ v • a := by simp [σ, LinearMap.toSpanSingleton]
      rw [h2] at h
      have hneg := congrArg (fun z => -z) h
      rw [neg_neg] at hneg
      exact hneg.symm
    have htv : t v = v + τ v := by
      change t v = v + (t v - v)
      abel
    rw [htv, hτv, sub_eq_add_neg]

theorem wSlpmC_isRefl_conj {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hd : 3 ≤ Module.finrank (ZMod p) U) (t₁ t₂ : U ≃ₗ[ZMod p] U)
    (ht₁ : IsRefl p t₁) (ht₂ : IsRefl p t₂) :
    ∃ g : U ≃ₗ[ZMod p] U, LinearEquiv.det g = 1 ∧ g * t₁ * g⁻¹ = t₂ := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp2
  obtain ⟨a, α, hα, hr⟩ := wSlpmC_isRefl_form h2 t₁ ht₁
  obtain ⟨b, β, hβ, hs⟩ := wSlpmC_isRefl_form h2 t₂ ht₂
  have hker : Module.finrank (ZMod p) ↥(LinearMap.ker α) =
      Module.finrank (ZMod p) ↥(LinearMap.ker β) := by
    rw [wSlpmC_finrank_ker a α hα h2, wSlpmC_finrank_ker b β hβ h2]
  let e₀ : ↥(LinearMap.ker α) ≃ₗ[ZMod p] ↥(LinearMap.ker β) :=
    LinearEquiv.ofFinrankEq _ _ hker
  set c : (ZMod p)ˣ := LinearEquiv.det (wSlpmC_glue a α hα h2 b β hβ e₀) with hc
  obtain ⟨φ, hφ⟩ := wSlpmC_exists_aut_det a α hα h2 hd c⁻¹
  refine ⟨wSlpmC_glue a α hα h2 b β hβ (φ.trans e₀), ?_, ?_⟩
  · rw [wSlpmC_glue_mul_block, map_mul, wSlpmC_block_det, hφ, ← hc]
    exact mul_inv_cancel c
  · exact wSlpmC_glue_conj_of a b α β hα hβ h2 t₁ t₂ hr hs (φ.trans e₀)

end CFSG.StandardType.ZS

end