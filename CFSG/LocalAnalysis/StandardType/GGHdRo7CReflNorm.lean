module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps
import CFSG.RankThree.PartOne.S12.Sec138LocLinear

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CNormRAux_two_eq_neg_one : (2 : ZMod 3) = -1 := by decide

private theorem hdRo7CNormRAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private theorem hdRo7CNormRAux_zmod3_ne_zero_cases :
    ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide

private noncomputable def hdRo7CNormRAux_T {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) : V →ₗ[ZMod p] V :=
  b.constr (ZMod p) fun i => if i = 0 then b i else -b i

private theorem hdRo7CNormRAux_T_self {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    hdRo7CNormRAux_T b (b 0) = b 0 := by
  rw [hdRo7CNormRAux_T, Module.Basis.constr_basis, if_pos rfl]

private theorem hdRo7CNormRAux_T_ne {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) {i : Fin (n + 1)} (hi : i ≠ 0) :
    hdRo7CNormRAux_T b (b i) = -b i := by
  rw [hdRo7CNormRAux_T, Module.Basis.constr_basis, if_neg hi]

private theorem hdRo7CNormRAux_T_comp {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    (hdRo7CNormRAux_T b).comp (hdRo7CNormRAux_T b) = LinearMap.id := by
  apply b.ext
  intro i
  by_cases hi : i = 0
  · subst hi
    simp [hdRo7CNormRAux_T_self b]
  · simp [hdRo7CNormRAux_T_ne b hi]

private theorem hdRo7CNormRAux_T_invol {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    Function.Involutive (hdRo7CNormRAux_T b) := by
  intro x
  have h := congrArg (fun L : V →ₗ[ZMod p] V => L x) (hdRo7CNormRAux_T_comp b)
  simpa [LinearMap.comp_apply] using h

private noncomputable def hdRo7CNormRAux_z {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) : V ≃ₗ[ZMod p] V :=
  LinearEquiv.ofInvolutive (hdRo7CNormRAux_T b) (hdRo7CNormRAux_T_invol b)

private theorem hdRo7CNormRAux_z_self {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) :
    hdRo7CNormRAux_z b (b 0) = b 0 := by
  simp only [hdRo7CNormRAux_z, LinearEquiv.coe_ofInvolutive]
  exact hdRo7CNormRAux_T_self b

private theorem hdRo7CNormRAux_z_ne {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) {i : Fin (n + 1)} (hi : i ≠ 0) :
    hdRo7CNormRAux_z b (b i) = -b i := by
  simp only [hdRo7CNormRAux_z, LinearEquiv.coe_ofInvolutive]
  exact hdRo7CNormRAux_T_ne b hi

private theorem hdRo7CNormRAux_z_invol {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (x : V) :
    hdRo7CNormRAux_z b (hdRo7CNormRAux_z b x) = x := by
  simp only [hdRo7CNormRAux_z, LinearEquiv.coe_ofInvolutive]
  exact hdRo7CNormRAux_T_invol b x

private theorem hdRo7CNormRAux_z_apply {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (v : V) :
    hdRo7CNormRAux_z b v = (2 * b.coord 0 v) • b 0 - v := by
  have hTapply : hdRo7CNormRAux_T b v = (2 * b.coord 0 v) • b 0 - v := by
    have hlin : hdRo7CNormRAux_T b =
        (2 : ZMod p) • (b.coord 0).smulRight (b 0) - LinearMap.id := by
      apply b.ext
      intro i
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply]
      by_cases hi : i = 0
      · subst hi
        rw [hdRo7CNormRAux_T_self b]
        simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, two_smul]
      · rw [hdRo7CNormRAux_T_ne b hi]
        simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hi, two_smul]
    have h := congrArg (fun L : V →ₗ[ZMod p] V => L v) hlin
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.id_apply, ← smul_smul] using h
  simpa only [hdRo7CNormRAux_z, LinearEquiv.coe_ofInvolutive] using hTapply

private theorem hdRo7CNormRAux_coord_ne
    {p : ℕ} [Fact p.Prime] (hp : p = 3) {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hP : ∀ a, C2SP p b a → a ∈ A)
    (hNoT : ∀ a ∈ A, ¬ C2Transv p a)
    (r : V ≃ₗ[ZMod p] V) (hr : r ∈ A)
    (u : V) (φ : V →ₗ[ZMod p] ZMod p)
    (hform : ∀ v, r v = v - φ v • u)
    (hφu : φ u = 2) (hφ0 : φ (b 0) = 1) (hu : u ≠ 0) :
    b.coord 0 u ≠ 0 := by
  subst hp
  intro hcoord
  have hzP : C2SP 3 b (hdRo7CNormRAux_z b) := by
    refine ⟨Equiv.refl _, fun i => if i = 0 then (1 : ZMod 3) else -1, rfl, by simp, ?_, ?_⟩
    · intro i; by_cases hi : i = 0 <;> simp [hi]
    · intro i
      by_cases hi : i = 0
      · subst hi; rw [hdRo7CNormRAux_z_self b]; simp
      · rw [hdRo7CNormRAux_z_ne b hi]; simp [hi]
  have hzA : hdRo7CNormRAux_z b ∈ A := hP _ hzP
  have hzu : hdRo7CNormRAux_z b u = -u := by
    rw [hdRo7CNormRAux_z_apply b u, hcoord]; simp
  have hru : r u = -u := by
    rw [hform u, hφu, two_smul]; abel
  let r' : V ≃ₗ[ZMod 3] V := hdRo7CNormRAux_z b * r * hdRo7CNormRAux_z b
  let t : V ≃ₗ[ZMod 3] V := r * r'
  have hr'A : r' ∈ A := A.mul_mem (A.mul_mem hzA hr) hzA
  have htA : t ∈ A := A.mul_mem hr hr'A
  have hr'_apply : ∀ v, r' v = v + φ (hdRo7CNormRAux_z b v) • u := by
    intro v
    show (hdRo7CNormRAux_z b * r * hdRo7CNormRAux_z b) v = _
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hform (hdRo7CNormRAux_z b v),
      map_sub, map_smul, hdRo7CNormRAux_z_invol b v, hzu, smul_neg, sub_neg_eq_add]
  have hzv_add : ∀ v, v + hdRo7CNormRAux_z b v = (2 * b.coord 0 v) • b 0 := by
    intro v
    rw [hdRo7CNormRAux_z_apply b v]
    abel
  have ht_apply : ∀ v, t v = v + b.coord 0 v • u := by
    intro v
    have hsum : (2 * b.coord 0 v : ZMod 3) =
        φ v + φ (hdRo7CNormRAux_z b v) := by
      rw [← map_add, hzv_add v, map_smul, hφ0, smul_eq_mul, mul_one]
    have h1 : t v = v - (2 * b.coord 0 v) • u := by
      show (r * r') v = _
      rw [LinearEquiv.mul_apply, hr'_apply v, map_add, map_smul, hform v, hru, hsum,
        add_smul, smul_neg]
      abel
    rw [h1]
    have h2 := hdRo7CNormRAux_two_eq_neg_one
    have h3 : (2 : ZMod 3) * b.coord 0 v = -(b.coord 0 v) := by rw [h2, neg_one_mul]
    rw [h3, neg_smul, sub_neg_eq_add]
  have ht_transv : C2Transv 3 t := by
    constructor
    · have hrange : ggLinMove t = Submodule.span (ZMod 3) {u} := by
        apply le_antisymm
        · intro x hx
          change x ∈ LinearMap.range (t.toLinearMap - LinearMap.id) at hx
          rw [LinearMap.mem_range] at hx
          obtain ⟨v, rfl⟩ := hx
          change t v - v ∈ Submodule.span (ZMod 3) {u}
          rw [ht_apply v, add_sub_cancel_left]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          change u ∈ LinearMap.range (t.toLinearMap - LinearMap.id)
          rw [LinearMap.mem_range]
          refine ⟨b 0, ?_⟩
          change t (b 0) - b 0 = u
          rw [ht_apply (b 0), Module.Basis.coord_apply, Module.Basis.repr_self]
          simp
      rw [hrange]
      exact finrank_span_singleton hu
    · intro w
      have htw : t w - w = b.coord 0 w • u := by rw [ht_apply w, add_sub_cancel_left]
      rw [htw, map_smul, ht_apply u, hcoord, zero_smul, add_zero]
  exact hNoT t htA ht_transv

theorem c2_reflNorm_holds : C2ReflNormLeaf := by
  intro p hp_fact hp n hn V _ _ b A hP hStab hNoT r hr hrefl hr0
  subst hp
  have hNop : CFSG.RankThree.PartOne.ReflF.Nop r = -(r.toLinearMap - LinearMap.id) := by
    ext x
    rw [CFSG.RankThree.PartOne.ReflF.Nop_apply, LinearMap.neg_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    abel
  have hrankNop : Module.finrank (ZMod 3)
      (LinearMap.range (CFSG.RankThree.PartOne.ReflF.Nop r)) = 1 := by
    rw [hNop, LinearMap.range_neg]
    exact hrefl.2
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  obtain ⟨u, φ, hd⟩ := CFSG.RankThree.PartOne.Sec138Loc.exists_reflData_field
    (K := ZMod 3) hdRo7CNormRAux_two_ne_zero r hrefl.1 hrankNop
  have hu : u ≠ 0 := hd.ne
  have hform : ∀ v, r v = v - φ v • u := hd.apply
  have hφu : φ u = 2 := hd.pair
  have hφ0_ne : φ (b 0) ≠ 0 := by
    intro h
    exact hr0 (by rw [hform (b 0), h, zero_smul, sub_zero])
  have hφ0_cases : φ (b 0) = 1 ∨ φ (b 0) = -1 :=
    hdRo7CNormRAux_zmod3_ne_zero_cases _ hφ0_ne
  rcases hφ0_cases with h1 | hneg
  · have hc := hdRo7CNormRAux_coord_ne (p := 3) (hp := rfl) (n := n) b A hP hNoT r hr u φ
      hform hφu h1 hu
    exact ⟨u, φ, hr, hform, hφu, h1, hc⟩
  · have hform' : ∀ v, r v = v - (-φ) v • (-u) := by
      intro v
      rw [hform v]
      simp
    have hφu' : (-φ) (-u) = 2 := by
      simp only [LinearMap.neg_apply, map_neg, hφu, neg_neg]
    have hφ0' : (-φ) (b 0) = 1 := by
      simp only [LinearMap.neg_apply, hneg, neg_neg]
    have hu' : (-u) ≠ 0 := neg_ne_zero.mpr hu
    have hc := hdRo7CNormRAux_coord_ne (p := 3) (hp := rfl) (n := n) b A hP hNoT r hr (-u) (-φ)
      hform' hφu' hφ0' hu'
    exact ⟨-u, -φ, hr, hform', hφu', hφ0', hc⟩

end CFSG.StandardType.HdRo7C
