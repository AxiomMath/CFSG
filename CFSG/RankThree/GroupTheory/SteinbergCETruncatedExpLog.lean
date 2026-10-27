module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.GroupTheory

open Polynomial

section Poly

variable {K : Type*} [Field K]

@[expose] noncomputable def expPoly (K : Type*) [Field K] (d : ℕ) : K[X] :=
  ∑ j ∈ Finset.range d, monomial j ((j.factorial : K)⁻¹)

@[expose] noncomputable def logPoly (K : Type*) [Field K] (d : ℕ) : K[X] :=
  ∑ j ∈ Finset.Ico 1 d, monomial j ((-1 : K) ^ (j + 1) * (j : K)⁻¹)

theorem coeff_expPoly (d n : ℕ) :
    (expPoly K d).coeff n = if n < d then ((n.factorial : K)⁻¹) else 0 := by
  simp [expPoly, coeff_monomial]

theorem coeff_logPoly (d n : ℕ) :
    (logPoly K d).coeff n = if 1 ≤ n ∧ n < d then (-1 : K) ^ (n + 1) * (n : K)⁻¹ else 0 := by
  simp [logPoly, coeff_monomial]

theorem expPoly_coeff_zero {d : ℕ} (hd : 1 ≤ d) : (expPoly K d).coeff 0 = 1 := by
  rw [coeff_expPoly]
  simp [show 0 < d by omega]

theorem logPoly_coeff_zero (d : ℕ) : (logPoly K d).coeff 0 = 0 := by
  rw [coeff_logPoly]
  simp

theorem derivative_expPoly {d : ℕ} (hd : 1 ≤ d) (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) :
    derivative (expPoly K d) = expPoly K d - C (((d - 1).factorial : K)⁻¹) * X ^ (d - 1) := by
  ext n
  rw [coeff_derivative, coeff_sub, coeff_C_mul_X_pow, coeff_expPoly, coeff_expPoly]
  by_cases h1 : n + 1 < d
  · have h2 : n < d := by omega
    have h3 : n ≠ d - 1 := by omega
    have h4 : ((n + 1 : ℕ) : K) ≠ 0 := hK (n + 1) (by omega) h1
    simp only [h1, h2, h3, ↓reduceIte, sub_zero]
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm, ← mul_assoc]
    push_cast at h4 ⊢
    rw [mul_inv_cancel₀ h4, one_mul]
  · by_cases h2 : n < d
    · have h5 : n = d - 1 := by omega
      subst h5
      simp only [h1, h2, ↓reduceIte, zero_mul, sub_self]
    · have h5 : n ≠ d - 1 := by omega
      simp only [h1, h2, h5, ↓reduceIte, zero_mul, sub_self]

theorem derivative_logPoly {d : ℕ} (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) :
    derivative (logPoly K d) = ∑ i ∈ Finset.range (d - 1), (-X : K[X]) ^ i := by
  have hX : ∀ i : ℕ, (-X : K[X]) ^ i = C ((-1 : K) ^ i) * X ^ i := fun i => by
    rw [neg_pow, C_pow, C_neg, C_1]
  simp only [hX]
  ext n
  rw [coeff_derivative, coeff_logPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (d - 1)) n]
  by_cases h1 : n + 1 < d
  · have h2 : n ∈ Finset.range (d - 1) := Finset.mem_range.mpr (by omega)
    have h4 : ((n + 1 : ℕ) : K) ≠ 0 := hK (n + 1) (by omega) h1
    simp only [show 1 ≤ n + 1 by omega, h1, and_self, ↓reduceIte, h2]
    push_cast at h4 ⊢
    rw [mul_assoc, inv_mul_cancel₀ h4, mul_one, pow_succ, pow_succ, mul_assoc, neg_one_mul,
      neg_neg, mul_one]
  · have h2 : n ∉ Finset.range (d - 1) := fun h => h1 (by rw [Finset.mem_range] at h; omega)
    simp only [h1, and_false, ↓reduceIte, zero_mul, h2]

theorem one_add_X_mul_derivative_logPoly {d : ℕ}
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) :
    (1 + X) * derivative (logPoly K d) = 1 - (-X : K[X]) ^ (d - 1) := by
  rw [derivative_logPoly hK]
  have h := geom_sum_mul (-X : K[X]) (d - 1)
  linear_combination -h

theorem X_pow_dvd_of_ode {d : ℕ} (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) (α β : K)
    {D : K[X]} (h0 : D.coeff 0 = 0)
    (h : X ^ (d - 1) ∣ (1 + C α * X) * derivative D + C β * D) : X ^ d ∣ D := by
  rw [X_pow_dvd_iff]
  intro n hn
  induction n with
  | zero => exact h0
  | succ n ih =>
    have ihn := ih (by omega)
    have hc := (X_pow_dvd_iff.mp h) n (by omega)
    have h4 : ((n + 1 : ℕ) : K) ≠ 0 := hK (n + 1) (by omega) hn
    have hXD : ((C α * X) * derivative D).coeff n = α * D.coeff n * n := by
      rcases n with _ | m
      · simp
      · rw [mul_comm (C α) X, mul_assoc, coeff_X_mul, coeff_C_mul, coeff_derivative]
        push_cast
        ring
    simp only [coeff_add, add_mul, one_mul, hXD, coeff_C_mul, ihn, mul_zero, zero_mul, add_zero,
      coeff_derivative] at hc
    have h5 : (n : K) + 1 ≠ 0 := by
      push_cast at h4
      exact h4
    exact (mul_eq_zero.mp hc).resolve_right h5

theorem X_pow_dvd_logPoly_comp_expPoly {d : ℕ} (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) :
    X ^ d ∣ (logPoly K d).comp (expPoly K d - 1) - X := by
  set c : K := ((d - 1).factorial : K)⁻¹
  apply X_pow_dvd_of_ode hK 0 0
  · rw [coeff_zero_eq_eval_zero, eval_sub, eval_comp, eval_sub, eval_one, eval_X,
      ← coeff_zero_eq_eval_zero, expPoly_coeff_zero hd, sub_self, ← coeff_zero_eq_eval_zero,
      logPoly_coeff_zero, sub_zero]
  obtain ⟨Q, hQ⟩ : X ∣ expPoly K d - 1 := by
    rw [X_dvd_iff, coeff_sub, coeff_one_zero, expPoly_coeff_zero hd, sub_self]
  have hLY : expPoly K d * (derivative (logPoly K d)).comp (expPoly K d - 1) =
      1 - (-(expPoly K d - 1)) ^ (d - 1) := by
    have h := congrArg (fun P => P.comp (expPoly K d - 1)) (one_add_X_mul_derivative_logPoly hK)
    simp only [mul_comp, add_comp, one_comp, X_comp, sub_comp, pow_comp, neg_comp] at h
    rwa [add_sub_cancel] at h
  have hpow : (-(expPoly K d - 1)) ^ (d - 1) = X ^ (d - 1) * (-Q) ^ (d - 1) := by
    rw [hQ, ← mul_neg, mul_pow]
  refine ⟨-(-Q) ^ (d - 1) - C c * (derivative (logPoly K d)).comp (expPoly K d - 1), ?_⟩
  rw [C_0, zero_mul, add_zero, zero_mul, add_zero, one_mul, derivative_sub, derivative_comp,
    derivative_X, derivative_sub, derivative_one, sub_zero, derivative_expPoly hd hK]
  linear_combination hLY - hpow

theorem X_pow_dvd_expPoly_comp_logPoly {d : ℕ} (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) :
    X ^ d ∣ (expPoly K d).comp (logPoly K d) - (1 + X) := by
  set c : K := ((d - 1).factorial : K)⁻¹
  apply X_pow_dvd_of_ode hK 1 (-1)
  · rw [coeff_zero_eq_eval_zero, eval_sub, eval_comp, eval_add, eval_one, eval_X, add_zero,
      ← coeff_zero_eq_eval_zero, logPoly_coeff_zero, ← coeff_zero_eq_eval_zero,
      expPoly_coeff_zero hd, sub_self]
  obtain ⟨P, hP⟩ : X ∣ logPoly K d := by
    rw [X_dvd_iff]
    exact logPoly_coeff_zero d
  have hEL : (derivative (expPoly K d)).comp (logPoly K d) =
      (expPoly K d).comp (logPoly K d) - C c * logPoly K d ^ (d - 1) := by
    rw [derivative_expPoly hd hK, sub_comp, mul_comp, C_comp, pow_comp, X_comp]
  have hL := one_add_X_mul_derivative_logPoly (K := K) hK
  have hLpow : logPoly K d ^ (d - 1) = X ^ (d - 1) * P ^ (d - 1) := by rw [hP, mul_pow]
  have hneg : (-X : K[X]) ^ (d - 1) = (-1) ^ (d - 1) * X ^ (d - 1) := neg_pow X (d - 1)
  refine ⟨-((-1) ^ (d - 1) * (expPoly K d).comp (logPoly K d)) - C c * P ^ (d - 1) +
    (-1) ^ (d - 1) * C c * X ^ (d - 1) * P ^ (d - 1), ?_⟩
  rw [derivative_sub, derivative_comp, derivative_add, derivative_one, derivative_X, zero_add,
    hEL, C_1, one_mul, C_neg, C_1]
  linear_combination ((expPoly K d).comp (logPoly K d) - C c * logPoly K d ^ (d - 1)) * hL +
    (C c * logPoly K d ^ (d - 1) - (expPoly K d).comp (logPoly K d)) * hneg +
    ((-1) ^ (d - 1) * X ^ (d - 1) * C c - C c) * hLpow

theorem X_pow_dvd_expPoly_neg_mul_expPoly {d : ℕ} (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) :
    X ^ d ∣ (expPoly K d).comp (-X) * expPoly K d - 1 := by
  set c : K := ((d - 1).factorial : K)⁻¹
  apply X_pow_dvd_of_ode hK 0 0
  · rw [coeff_zero_eq_eval_zero, eval_sub, eval_mul, eval_comp, eval_neg, eval_X, neg_zero,
      eval_one, ← coeff_zero_eq_eval_zero, expPoly_coeff_zero hd, mul_one, sub_self]
  have hE := derivative_expPoly (K := K) hd hK
  have hE' : (derivative (expPoly K d)).comp (-X) =
      (expPoly K d).comp (-X) - C c * (-X) ^ (d - 1) := by
    rw [hE, sub_comp, mul_comp, C_comp, pow_comp, X_comp]
  have hneg : (-X : K[X]) ^ (d - 1) = (-1) ^ (d - 1) * X ^ (d - 1) := neg_pow X (d - 1)
  refine ⟨C c * (-1) ^ (d - 1) * expPoly K d - C c * (expPoly K d).comp (-X), ?_⟩
  rw [C_0, zero_mul, add_zero, zero_mul, add_zero, one_mul, derivative_sub, derivative_one,
    sub_zero, derivative_mul, derivative_comp, derivative_neg, derivative_X, hE', hE]
  linear_combination C c * expPoly K d * hneg

end Poly

section Matrix

variable {K : Type*} [Field K] {d : ℕ}

@[expose] def truncExp (d : ℕ) (N : Matrix (Fin d) (Fin d) K) : Matrix (Fin d) (Fin d) K :=
  ∑ j ∈ Finset.range d, ((j.factorial : K)⁻¹) • N ^ j

@[expose] def truncLog (d : ℕ) (u : Matrix (Fin d) (Fin d) K) : Matrix (Fin d) (Fin d) K :=
  ∑ j ∈ Finset.Ico 1 d, ((-1 : K) ^ (j + 1) * (j : K)⁻¹) • (u - 1) ^ j

theorem aeval_expPoly (N : Matrix (Fin d) (Fin d) K) : aeval N (expPoly K d) = truncExp d N := by
  simp only [expPoly, map_sum, aeval_monomial, truncExp, Algebra.smul_def]

theorem aeval_logPoly (u : Matrix (Fin d) (Fin d) K) :
    aeval (u - 1) (logPoly K d) = truncLog d u := by
  simp only [logPoly, map_sum, aeval_monomial, truncLog, Algebra.smul_def]

theorem aeval_eq_of_X_pow_dvd {N : Matrix (Fin d) (Fin d) K} (hN : N ^ d = 0) {P Q : K[X]}
    (h : X ^ d ∣ P - Q) : aeval N P = aeval N Q := by
  obtain ⟨S, hS⟩ := h
  rw [← sub_eq_zero, ← map_sub, hS, map_mul, map_pow, aeval_X, hN, zero_mul]

theorem matrix_pow_eq_zero_of_isNilpotent {N : Matrix (Fin d) (Fin d) K} (hN : IsNilpotent N) :
    N ^ d = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have h2 : N.charpoly = X ^ Fintype.card (Fin d) := sub_eq_zero.mp h.eq_zero
  have h3 := Matrix.aeval_self_charpoly N
  rwa [h2, map_pow, aeval_X, Fintype.card_fin] at h3

theorem truncLog_truncExp (hd : 1 ≤ d) (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0)
    {N : Matrix (Fin d) (Fin d) K} (hN : N ^ d = 0) : truncLog d (truncExp d N) = N := by
  rw [← aeval_logPoly, ← aeval_expPoly, ← map_one (aeval (R := K) N), ← map_sub, ← aeval_comp,
    aeval_eq_of_X_pow_dvd hN (X_pow_dvd_logPoly_comp_expPoly hd hK), aeval_X]

theorem truncExp_truncLog (hd : 1 ≤ d) (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0)
    {u : Matrix (Fin d) (Fin d) K} (hu : (u - 1) ^ d = 0) : truncExp d (truncLog d u) = u := by
  rw [← aeval_logPoly, ← aeval_expPoly, ← aeval_comp,
    aeval_eq_of_X_pow_dvd hu (X_pow_dvd_expPoly_comp_logPoly hd hK), map_add, map_one, aeval_X,
    add_sub_cancel]

theorem truncExp_neg_mul_truncExp (hd : 1 ≤ d) (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0)
    {N : Matrix (Fin d) (Fin d) K} (hN : N ^ d = 0) : truncExp d (-N) * truncExp d N = 1 := by
  have h := aeval_eq_of_X_pow_dvd hN (X_pow_dvd_expPoly_neg_mul_expPoly hd hK)
  rwa [map_mul, aeval_comp, map_neg, aeval_X, aeval_expPoly, aeval_expPoly, map_one] at h

theorem truncExp_sub_one_pow (hd : 1 ≤ d) {N : Matrix (Fin d) (Fin d) K} (hN : N ^ d = 0) :
    (truncExp d N - 1) ^ d = 0 := by
  obtain ⟨Q, hQ⟩ : X ∣ expPoly K d - 1 := by
    rw [X_dvd_iff, coeff_sub, coeff_one_zero, expPoly_coeff_zero hd, sub_self]
  rw [← aeval_expPoly, ← map_one (aeval (R := K) N), ← map_sub, ← map_pow, hQ, mul_pow, map_mul,
    map_pow,
    aeval_X, hN, zero_mul]

theorem truncLog_pow {u : Matrix (Fin d) (Fin d) K} (hu : (u - 1) ^ d = 0) :
    truncLog d u ^ d = 0 := by
  obtain ⟨P, hP⟩ : X ∣ logPoly K d := by
    rw [X_dvd_iff]
    exact logPoly_coeff_zero d
  rw [← aeval_logPoly, ← map_pow, hP, mul_pow, map_mul, map_pow, aeval_X, hu, zero_mul]

theorem truncExp_conj (g : (Matrix (Fin d) (Fin d) K)ˣ) (N : Matrix (Fin d) (Fin d) K) :
    truncExp d ((g : Matrix (Fin d) (Fin d) K) * N * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K)) =
      g * truncExp d N * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K) := by
  simp only [truncExp, Units.conj_pow, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]

theorem truncLog_conj (g : (Matrix (Fin d) (Fin d) K)ˣ) (u : Matrix (Fin d) (Fin d) K) :
    truncLog d ((g : Matrix (Fin d) (Fin d) K) * u * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K)) =
      g * truncLog d u * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K) := by
  have h : (g : Matrix (Fin d) (Fin d) K) * u * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K) - 1 =
      g * (u - 1) * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K) := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
  simp only [truncLog, h, Units.conj_pow, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]

theorem truncExp_map (σ : K →+* K) (N : Matrix (Fin d) (Fin d) K) :
    truncExp d (N.map σ) = (truncExp d N).map σ := by
  ext i j
  simp only [truncExp, ← Matrix.map_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]

theorem truncLog_map (σ : K →+* K) (u : Matrix (Fin d) (Fin d) K) :
    truncLog d (u.map σ) = (truncLog d u).map σ := by
  have h : u.map σ - 1 = (u - 1).map σ := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_sub, map_one]
  ext i j
  simp only [truncLog, h, ← Matrix.map_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast, map_pow, map_neg, map_one]

theorem commute_truncExp_iff (hd : 1 ≤ d) (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0)
    {N : Matrix (Fin d) (Fin d) K} (hN : N ^ d = 0) (Y : Matrix (Fin d) (Fin d) K) :
    Commute Y (truncExp d N) ↔ Commute Y N := by
  constructor
  · intro h
    have h1 : Commute Y (truncExp d N - 1) := h.sub_right (Commute.one_right Y)
    have h2 : Commute Y (truncLog d (truncExp d N)) :=
      Commute.sum_right _ _ _ fun j _ => (h1.pow_right j).smul_right _
    rwa [truncLog_truncExp hd hK hN] at h2
  · intro h
    exact Commute.sum_right _ _ _ fun j _ => (h.pow_right j).smul_right _

theorem dagger_truncExp (C : (Matrix (Fin d) (Fin d) K)ˣ) (N : Matrix (Fin d) (Fin d) K) :
    (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * (truncExp d N).transpose *
        (C : Matrix (Fin d) (Fin d) K) =
      truncExp d ((↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * N.transpose *
        (C : Matrix (Fin d) (Fin d) K)) := by
  simp only [truncExp, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_pow,
    Units.conj_pow', Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

theorem dagger_truncLog (C : (Matrix (Fin d) (Fin d) K)ˣ) (u : Matrix (Fin d) (Fin d) K) :
    (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * (truncLog d u).transpose *
        (C : Matrix (Fin d) (Fin d) K) =
      truncLog d ((↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * u.transpose *
        (C : Matrix (Fin d) (Fin d) K)) := by
  have h : (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * u.transpose *
        (C : Matrix (Fin d) (Fin d) K) - 1 =
      (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * (u - 1).transpose *
        (C : Matrix (Fin d) (Fin d) K) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, mul_sub, sub_mul, mul_one, Units.inv_mul]
  simp only [truncLog, h, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_pow,
    Units.conj_pow', Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

end Matrix

open Matrix in
theorem small_bilinear_isometry_unipotent_logarithm_calculus {K : Type*} [Field K] {p : ℕ}
    [Fact p.Prime] [CharP K p] {d : ℕ} (hd : 1 ≤ d) (hdp : d ≤ p) :
    (∀ N : Matrix (Fin d) (Fin d) K, IsNilpotent N →
      IsNilpotent (truncExp d N - 1) ∧ truncLog d (truncExp d N) = N) ∧
    (∀ u : Matrix (Fin d) (Fin d) K, IsNilpotent (u - 1) →
      IsNilpotent (truncLog d u) ∧ truncExp d (truncLog d u) = u) ∧
    (∀ (g : GeneralLinearGroup (Fin d) K) (N : Matrix (Fin d) (Fin d) K),
      truncExp d ((g : Matrix (Fin d) (Fin d) K) * N * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K)) =
        g * truncExp d N * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K)) ∧
    (∀ (g : GeneralLinearGroup (Fin d) K) (u : Matrix (Fin d) (Fin d) K),
      truncLog d ((g : Matrix (Fin d) (Fin d) K) * u * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K)) =
        g * truncLog d u * (↑(g⁻¹) : Matrix (Fin d) (Fin d) K)) ∧
    (∀ (σ : K →+* K) (N : Matrix (Fin d) (Fin d) K),
      truncExp d (N.map σ) = (truncExp d N).map σ) ∧
    (∀ (σ : K →+* K) (u : Matrix (Fin d) (Fin d) K),
      truncLog d (u.map σ) = (truncLog d u).map σ) ∧
    (∀ N : Matrix (Fin d) (Fin d) K, IsNilpotent N → ∀ g : GeneralLinearGroup (Fin d) K,
      Commute (g : Matrix (Fin d) (Fin d) K) (truncExp d N) ↔
        Commute (g : Matrix (Fin d) (Fin d) K) N) ∧
    (∀ u : Matrix (Fin d) (Fin d) K, IsNilpotent (u - 1) → u ^ p = 1) ∧
    ∀ C : GeneralLinearGroup (Fin d) K,
      (∀ N : Matrix (Fin d) (Fin d) K, IsNilpotent N →
        (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * Nᵀ * (C : Matrix (Fin d) (Fin d) K) = -N →
        IsNilpotent (truncExp d N - 1) ∧
          (truncExp d N)ᵀ * (C : Matrix (Fin d) (Fin d) K) * truncExp d N = C) ∧
      (∀ u : Matrix (Fin d) (Fin d) K, IsNilpotent (u - 1) →
        uᵀ * (C : Matrix (Fin d) (Fin d) K) * u = C →
        IsNilpotent (truncLog d u) ∧
          (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * (truncLog d u)ᵀ *
            (C : Matrix (Fin d) (Fin d) K) = -truncLog d u) := by
  have hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0 := fun n hn hnd h =>
    Nat.not_dvd_of_pos_of_lt hn (by omega) ((CharP.cast_eq_zero_iff K p n).mp h)
  have hnil : ∀ N : Matrix (Fin d) (Fin d) K, IsNilpotent N ↔ N ^ d = 0 :=
    fun N => ⟨matrix_pow_eq_zero_of_isNilpotent, fun h => ⟨d, h⟩⟩
  refine ⟨fun N hN => ?_, fun u hu => ?_, fun g N => truncExp_conj g N,
    fun g u => truncLog_conj g u, fun σ N => truncExp_map σ N, fun σ u => truncLog_map σ u,
    fun N hN g => commute_truncExp_iff hd hK ((hnil N).mp hN) _, fun u hu => ?_,
    fun C => ⟨fun N hN hNC => ?_, fun u hu huC => ?_⟩⟩
  · have hN' := (hnil N).mp hN
    exact ⟨(hnil _).mpr (truncExp_sub_one_pow hd hN'), truncLog_truncExp hd hK hN'⟩
  · have hu' := (hnil _).mp hu
    exact ⟨(hnil _).mpr (truncLog_pow hu'), truncExp_truncLog hd hK hu'⟩
  ·
    have hu' := (hnil _).mp hu
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have h1 : (u - 1) ^ p = 0 := by
      rw [← Nat.sub_add_cancel hdp, pow_add, hu', mul_zero]
    calc u ^ p = (1 + (u - 1)) ^ p := by rw [add_sub_cancel]
      _ = 1 ^ p + (u - 1) ^ p := add_pow_char_of_commute p (Commute.one_left _)
      _ = 1 := by rw [one_pow, h1, add_zero]
  ·
    have hN' := (hnil N).mp hN
    refine ⟨(hnil _).mpr (truncExp_sub_one_pow hd hN'), ?_⟩
    have h1 := dagger_truncExp C N
    rw [hNC] at h1
    calc (truncExp d N)ᵀ * (C : Matrix (Fin d) (Fin d) K) * truncExp d N =
          C * ((↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * (truncExp d N)ᵀ *
            (C : Matrix (Fin d) (Fin d) K)) * truncExp d N := by
          rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
      _ = C * (truncExp d (-N) * truncExp d N) := by rw [h1, mul_assoc]
      _ = C := by rw [truncExp_neg_mul_truncExp hd hK hN', mul_one]
  ·
    have hu' := (hnil _).mp hu
    set N := truncLog d u with hN
    have hN' : N ^ d = 0 := truncLog_pow hu'
    refine ⟨(hnil _).mpr hN', ?_⟩
    have hexp : truncExp d N = u := truncExp_truncLog hd hK hu'
    have hdag1 : (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * uᵀ * (C : Matrix (Fin d) (Fin d) K) * u =
        1 := by
      rw [mul_assoc, mul_assoc, ← mul_assoc uᵀ, huC, Units.inv_mul]
    have hinv : truncExp d (-N) * u = 1 := by
      rw [← hexp]
      exact truncExp_neg_mul_truncExp hd hK hN'
    have hdag : (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * uᵀ * (C : Matrix (Fin d) (Fin d) K) =
        truncExp d (-N) := by
      have h2 : u * truncExp d (-N) = 1 := mul_eq_one_comm.mp hinv
      calc (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * uᵀ * (C : Matrix (Fin d) (Fin d) K) =
            (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) * uᵀ * (C : Matrix (Fin d) (Fin d) K) *
              (u * truncExp d (-N)) := by rw [h2, mul_one]
        _ = truncExp d (-N) := by rw [← mul_assoc, hdag1, one_mul]
    have hneg : (-N) ^ d = 0 := by rw [neg_pow, hN', mul_zero]
    rw [dagger_truncLog, hdag, truncLog_truncExp hd hK hneg]

end CFSG.RankThree.GroupTheory
