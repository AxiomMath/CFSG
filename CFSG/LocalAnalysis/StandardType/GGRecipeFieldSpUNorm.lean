module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

namespace RecipeFieldSpU

open Matrix

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def twNorm (σ : k ≃+* k) (M : Matrix ι ι k) : ℕ → Matrix ι ι k
  | 0 => 1
  | j + 1 => M * (twNorm σ M j).map σ

theorem twNorm_zero (σ : k ≃+* k) (M : Matrix ι ι k) : twNorm σ M 0 = 1 :=
  rfl

theorem twNorm_succ (σ : k ≃+* k) (M : Matrix ι ι k) (j : ℕ) :
    twNorm σ M (j + 1) = M * (twNorm σ M j).map σ :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem map_map_ringEquiv (σ τ : k ≃+* k) (X : Matrix ι ι k) :
    (X.map τ).map σ = X.map ⇑(σ * τ) := by
  rw [Matrix.map_map]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem map_pow_zero (σ : k ≃+* k) (X : Matrix ι ι k) : X.map ⇑(σ ^ 0) = X := by
  ext i j
  rfl

omit [DecidableEq ι] in
theorem map_mul_ringEquiv (σ : k ≃+* k) (X Y : Matrix ι ι k) : (X * Y).map σ = X.map σ * Y.map σ :=
  Matrix.map_mul (f := (σ : k →+* k))

omit [Fintype ι] [DecidableEq ι] in
theorem map_smul_ringEquiv (σ : k ≃+* k) (a : k) (X : Matrix ι ι k) :
    (a • X).map σ = σ a • X.map σ := by
  ext i j
  simp

omit [Fintype ι] in
theorem map_one_ringEquiv (σ : k ≃+* k) : (1 : Matrix ι ι k).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem twNorm_succ' (σ : k ≃+* k) (M : Matrix ι ι k) (j : ℕ) :
    twNorm σ M (j + 1) = twNorm σ M j * M.map ⇑(σ ^ j) := by
  induction j with
  | zero => rw [twNorm_succ, twNorm_zero, map_one_ringEquiv, Matrix.mul_one, Matrix.one_mul,
      map_pow_zero]
  | succ j ih =>
    rw [twNorm_succ, ih, map_mul_ringEquiv, map_map_ringEquiv, ← pow_succ', ← Matrix.mul_assoc,
      ← twNorm_succ, ih]

theorem twNorm_smul (σ : k ≃+* k) (c : k) (M : Matrix ι ι k) (j : ℕ) :
    twNorm σ (c • M) j = (∏ i ∈ Finset.range j, (σ ^ i) c) • twNorm σ M j := by
  induction j with
  | zero => rw [twNorm_zero, twNorm_zero, Finset.prod_range_zero, one_smul]
  | succ j ih =>
    rw [twNorm_succ, twNorm_succ, ih, map_smul_ringEquiv, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul,
      Finset.prod_range_succ', map_prod, pow_zero, mul_comm]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ']
    rfl

theorem isUnit_det_twNorm (σ : k ≃+* k) {M : Matrix ι ι k} (hM : IsUnit M.det) (j : ℕ) :
    IsUnit (twNorm σ M j).det := by
  induction j with
  | zero => rw [twNorm_zero, Matrix.det_one]; exact isUnit_one
  | succ j ih =>
    rw [twNorm_succ, Matrix.det_mul,
      show (twNorm σ M j).map σ = (σ : k →+* k).mapMatrix (twNorm σ M j) from rfl,
      ← RingHom.map_det]
    exact hM.mul (ih.map _)

omit [DecidableEq ι] in
theorem comp_mulVec (σ : k ≃+* k) (X : Matrix ι ι k) (w : ι → k) :
    σ ∘ (X *ᵥ w) = X.map σ *ᵥ (σ ∘ w) :=
  funext fun i => RingHom.map_mulVec (σ : k →+* k) X w i

theorem twNorm_mulVec_iterate (σ : k ≃+* k) (M : Matrix ι ι k) (j : ℕ) (v : ι → k) :
    (fun w : ι → k => M *ᵥ (σ ∘ w))^[j] v = twNorm σ M j *ᵥ (⇑(σ ^ j) ∘ v) := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, twNorm_zero, Matrix.one_mulVec]; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, comp_mulVec, Matrix.mulVec_mulVec, ← twNorm_succ,
      pow_succ']
    rfl

theorem iterate_mul_map_apply (σ : k ≃+* k) (μ : k) (j : ℕ) (x : k) :
    (fun y : k => μ * σ y)^[j] x = (∏ i ∈ Finset.range j, (σ ^ i) μ) * (σ ^ j) x := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, Finset.prod_range_zero, one_mul]; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [map_mul, map_prod, Finset.prod_range_succ', pow_zero, pow_succ', RingAut.mul_apply,
      RingAut.one_apply]
    ring

omit [Fintype ι] [DecidableEq ι] in
theorem map_pow_eq_prod_smul (σ : k ≃+* k) {μ : k} {B : Matrix ι ι k} (hB : B.map σ = μ • B)
    (j : ℕ) : B.map ⇑(σ ^ j) = (∏ i ∈ Finset.range j, (σ ^ i) μ) • B := by
  induction j with
  | zero => rw [map_pow_zero, Finset.prod_range_zero, one_smul]
  | succ j ih =>
    rw [pow_succ', ← map_map_ringEquiv, ih, map_smul_ringEquiv, hB, smul_smul]
    congr 1
    rw [map_prod σ, Finset.prod_range_succ' (fun i => (σ ^ i) μ), pow_zero]
    simp only [pow_succ', RingAut.mul_apply, RingAut.one_apply]

theorem exists_mul_map_eq_smul_of_twNorm [Finite k] [Nonempty ι] {σ : k ≃+* k} {h : ℕ}
    (hσ : orderOf σ = h) {M : Matrix ι ι k} (hM : IsUnit M.det) {c : k}
    (hc : twNorm σ M h = c • (1 : Matrix ι ι k)) :
    ∃ (X : Matrix ι ι k) (d : k), IsUnit X.det ∧ d ≠ 0 ∧ M * X.map σ = d • X := by
  classical
  have hσh : σ ^ h = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hone : M.map ⇑(1 : k ≃+* k) = M := by
    ext i j
    rfl
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, Matrix.det_zero] at hM
    exact not_isUnit_zero hM
  have hcfix : σ c = c := by
    have h1 := twNorm_succ' σ M h
    rw [twNorm_succ, hc, map_smul_ringEquiv, map_one_ringEquiv, hσh, hone, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h1
    have h3 : (σ c - c) • M = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hM0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hu := isUnit_det_twNorm σ hM h
    rw [hc, zero_smul, Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have : Finite (k ≃+* k) :=
    Finite.of_injective (fun τ : k ≃+* k => (τ : k → k)) (fun _ _ h => RingEquiv.ext (congrFun h))
  have hh : 0 < h := hσ ▸ orderOf_pos σ
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ hcfix
  rw [hσ] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hc0
    rw [← hd]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hh) (map_zero _)
  set M' : Matrix ι ι k := d⁻¹ • M with hM'
  have hM'u : IsUnit M'.det := by
    rw [hM', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hd0))).mul hM
  have hN' : twNorm σ M' h = 1 := by
    rw [hM', twNorm_smul, hc, smul_smul]
    have e1 : (∏ i ∈ Finset.range h, (σ ^ i) d⁻¹) * c = 1 := by
      simp only [map_inv₀, Finset.prod_inv_distrib]
      rw [hd]
      exact inv_mul_cancel₀ hc0
    rw [e1, one_smul]
  have hper : ∀ v : ι → k, (fun w : ι → k => M' *ᵥ (σ ∘ w))^[h] v = v := fun v => by
    rw [twNorm_mulVec_iterate, hN', Matrix.one_mulVec, hσh]
    rfl
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' k
  obtain ⟨B, hB, hfix⟩ := CFSG.RankThree.PartTwo.KFacts.exists_isUnit_det_fixed_index hℓ e.pos
    (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ M' hM'u hper
  refine ⟨B, d, hB, hd0, ?_⟩
  have h6 := congrArg (fun X => d • X) hfix
  simp only [hM', Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hd0, one_smul] at h6
  exact h6

end RecipeFieldSpU

end CFSG.StandardType
