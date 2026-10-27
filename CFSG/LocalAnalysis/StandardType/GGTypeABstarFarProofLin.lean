module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section LinRefl

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def IsLinRefl (T : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ (x : V) (f : Module.Dual (ZMod p) V), f x = 2 ∧ ∀ v, T v = v - f v • x

theorem IsLinRefl.apply_apply {T : V ≃ₗ[ZMod p] V} (h : IsLinRefl T) (v : V) : T (T v) = v := by
  obtain ⟨x, f, hfx, hT⟩ := h
  have hTeq : T = Module.reflection hfx := by
    ext w
    rw [hT w, Module.reflection_apply]
  rw [hTeq]
  exact Module.involutive_reflection hfx v

theorem IsLinRefl.exists_anti (hp2 : p ≠ 2) {T : V ≃ₗ[ZMod p] V} (h : IsLinRefl T) :
    ∃ v : V, v ≠ 0 ∧ T v = -v := by
  obtain ⟨x, f, hfx, hT⟩ := h
  obtain ⟨hx0, -⟩ := ne_zero_of_apply_eq_two hp2 hfx
  refine ⟨x, hx0, ?_⟩
  have hTeq : T = Module.reflection hfx := by
    ext w
    rw [hT w, Module.reflection_apply]
  rw [hTeq]
  exact Module.reflection_apply_self hfx

theorem IsLinRefl.ne_one (hp2 : p ≠ 2) {T : V ≃ₗ[ZMod p] V} (h : IsLinRefl T) : T ≠ 1 := by
  intro hT
  obtain ⟨v, hv0, hv⟩ := h.exists_anti hp2
  rw [hT] at hv
  have hv' : v = -v := by simpa using hv
  have h2v : (2 : ZMod p) • v = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hv'
  rcases (smul_eq_zero.mp h2v) with h2 | hv'
  · exact (zmod_two_ne_zero hp2) h2
  · exact hv0 hv'

private theorem bfLin_two_smul_eq_of_eigen {T : V ≃ₗ[ZMod p] V} {x : V}
    {f : Module.Dual (ZMod p) V} (hT : ∀ w, T w = w - f w • x) {v : V} (hv : T v = -v) :
    (2 : ZMod p) • v = f v • x := by
  have h : v - f v • x = -v := by
    have h' := hT v
    rw [hv] at h'
    exact h'.symm
  have hvv : v + v = f v • x := by
    have h' : v = -v + f v • x := sub_eq_iff_eq_add.mp h
    have hc := congrArg (· + v) h'
    rw [hc]
    abel
  rw [two_smul]
  exact hvv

theorem IsLinRefl.anti_eq_smul (hp2 : p ≠ 2) {T : V ≃ₗ[ZMod p] V} (h : IsLinRefl T) {v w : V}
    (hv : v ≠ 0) (hTv : T v = -v) (hTw : T w = -w) : ∃ c : ZMod p, w = c • v := by
  obtain ⟨x, f, hfx, hT⟩ := h
  have hv2 : (2 : ZMod p) • v = f v • x := bfLin_two_smul_eq_of_eigen hT hTv
  have hw2 : (2 : ZMod p) • w = f w • x := bfLin_two_smul_eq_of_eigen hT hTw
  have hfv : f v ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hv2
    rcases (smul_eq_zero.mp hv2) with h2 | hv'
    · exact (zmod_two_ne_zero hp2) h2
    · exact hv hv'
  have key : f v • w = f w • v := by
    have h1 : f v • ((2 : ZMod p) • w) = f w • ((2 : ZMod p) • v) := by
      rw [hw2, hv2, smul_smul, smul_smul, mul_comm]
    have h1' : (2 : ZMod p) • (f v • w) = (2 : ZMod p) • (f w • v) := by
      rw [← smul_comm (f v) (2 : ZMod p) w, ← smul_comm (f w) (2 : ZMod p) v]
      exact h1
    exact (smul_right_inj (zmod_two_ne_zero hp2)).mp h1'
  refine ⟨(f v)⁻¹ * f w, ?_⟩
  have h := congrArg ((f v)⁻¹ • ·) key
  rw [smul_smul, inv_mul_cancel₀ hfv, one_smul, smul_smul] at h
  exact h

private theorem bfLin_comm_eq_of_same_line (hp2 : p ≠ 2) {v : V} (hv0 : v ≠ 0)
    {g₁ g₂ : Module.Dual (ZMod p) V} (hg₁ : g₁ v = 2) (hg₂ : g₂ v = 2)
    {T₁ T₂ : V ≃ₗ[ZMod p] V} (hT₁ : ∀ w, T₁ w = w - g₁ w • v)
    (hT₂ : ∀ w, T₂ w = w - g₂ w • v) (hc : T₁ * T₂ = T₂ * T₁) : T₁ = T₂ := by
  ext w
  have hcomm : T₁ (T₂ w) = T₂ (T₁ w) := by
    have h := congrArg (fun T : V ≃ₗ[ZMod p] V => T w) hc
    simpa only [LinearEquiv.mul_apply] using h
  have hL : T₁ (T₂ w) = w - (g₁ w - g₂ w) • v := by
    rw [hT₂, hT₁]
    simp only [map_sub, map_smul, hg₁]
    module
  have hR : T₂ (T₁ w) = w + (g₁ w - g₂ w) • v := by
    rw [hT₁, hT₂]
    simp only [map_sub, map_smul, hg₂]
    module
  rw [hL, hR] at hcomm
  set A : V := (g₁ w - g₂ w) • v with hA
  have hφ : g₁ w - g₂ w = 0 := by
    have h2 : (2 : ZMod p) • A = 0 := by
      rw [two_smul]
      have h' : w + 0 = w + (A + A) := by
        rw [add_zero, ← add_assoc]
        exact sub_eq_iff_eq_add.mp hcomm
      exact (add_left_cancel h').symm
    rcases (smul_eq_zero.mp h2) with h0 | h0
    · exact absurd h0 (zmod_two_ne_zero hp2)
    · rw [hA, sub_smul, sub_eq_zero] at h0
      exact sub_eq_zero.mpr ((smul_left_inj hv0).mp h0)
  rw [sub_eq_zero] at hφ
  rw [hT₁, hT₂, hφ]

theorem IsLinRefl.comm_fix (hp2 : p ≠ 2) {T₁ T₂ : V ≃ₗ[ZMod p] V} (h₁ : IsLinRefl T₁)
    (h₂ : IsLinRefl T₂) (hc : T₁ * T₂ = T₂ * T₁) (hne : T₁ ≠ T₂) {v : V} (hv : T₁ v = -v) :
    T₂ v = v := by
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  have h2 := zmod_two_ne_zero hp2
  have hT₁v : T₁ (T₂ v) = -(T₂ v) := by
    have h := congrArg (fun T : V ≃ₗ[ZMod p] V => T v) hc
    simp only [LinearEquiv.mul_apply] at h
    rw [hv, map_neg] at h
    exact h
  obtain ⟨c, hcdef⟩ := h₁.anti_eq_smul hp2 hv0 hv hT₁v
  have hcc : c * c = 1 := by
    have h := h₂.apply_apply v
    rw [hcdef, map_smul, hcdef, smul_smul] at h
    have h' : (c * c) • v = (1 : ZMod p) • v := by rw [h, one_smul]
    exact (smul_left_inj hv0).mp h'
  rcases (mul_self_eq_one_iff.mp hcc) with hc1 | hc1
  · rw [hcdef, hc1, one_smul]
  · exfalso
    have hv₂ : T₂ v = -v := by rw [hcdef, hc1, neg_one_smul]
    obtain ⟨x₁, f₁, hf₁, hT₁⟩ := h₁
    obtain ⟨x₂, f₂, hf₂, hT₂⟩ := h₂
    have hv2₁ : (2 : ZMod p) • v = f₁ v • x₁ := bfLin_two_smul_eq_of_eigen hT₁ hv
    have hv2₂ : (2 : ZMod p) • v = f₂ v • x₂ := bfLin_two_smul_eq_of_eigen hT₂ hv₂
    have hf₁v : f₁ v ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hv2₁
      rcases (smul_eq_zero.mp hv2₁) with h' | h'
      · exact h2 h'
      · exact hv0 h'
    have hf₂v : f₂ v ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hv2₂
      rcases (smul_eq_zero.mp hv2₂) with h' | h'
      · exact h2 h'
      · exact hv0 h'
    have hx₁ : x₁ = ((f₁ v)⁻¹ * 2) • v := by
      have h := congrArg ((f₁ v)⁻¹ • ·) hv2₁
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hf₁v, one_smul] at h
      exact h.symm
    have hx₂ : x₂ = ((f₂ v)⁻¹ * 2) • v := by
      have h := congrArg ((f₂ v)⁻¹ • ·) hv2₂
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hf₂v, one_smul] at h
      exact h.symm
    set c₁ : ZMod p := (f₁ v)⁻¹ * 2 with hc₁
    set c₂ : ZMod p := (f₂ v)⁻¹ * 2 with hc₂
    have hx₁' : x₁ = c₁ • v := by rw [hc₁]; exact hx₁
    have hx₂' : x₂ = c₂ • v := by rw [hc₂]; exact hx₂
    have hg₁ : (c₁ • f₁) v = 2 := by
      rw [LinearMap.smul_apply, smul_eq_mul, hc₁, mul_assoc, mul_comm 2 (f₁ v),
        ← mul_assoc, inv_mul_cancel₀ hf₁v, one_mul]
    have hg₂ : (c₂ • f₂) v = 2 := by
      rw [LinearMap.smul_apply, smul_eq_mul, hc₂, mul_assoc, mul_comm 2 (f₂ v),
        ← mul_assoc, inv_mul_cancel₀ hf₂v, one_mul]
    have hT₁' : ∀ w, T₁ w = w - (c₁ • f₁) w • v := by
      intro w
      have hw : f₁ w • (c₁ • v) = (c₁ • f₁) w • v := by
        rw [smul_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
      rw [hT₁ w, hx₁', hw]
    have hT₂' : ∀ w, T₂ w = w - (c₂ • f₂) w • v := by
      intro w
      have hw : f₂ w • (c₂ • v) = (c₂ • f₂) w • v := by
        rw [smul_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
      rw [hT₂ w, hx₂', hw]
    exact hne (bfLin_comm_eq_of_same_line hp2 hv0 hg₁ hg₂ hT₁' hT₂' hc)

end LinRefl

end CFSG.StandardType
