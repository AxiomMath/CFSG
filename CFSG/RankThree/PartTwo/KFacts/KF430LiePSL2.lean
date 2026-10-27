module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF430

open Matrix Polynomial

variable {F : Type*} [CommRing F]

@[expose] def uMat : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, -1]

theorem uMat_sq : uMat (F := F) ^ 2 = !![-1, 1; -1, 0] := by
  rw [sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem uMat_cube : uMat (F := F) ^ 3 = 1 := by
  rw [pow_succ, uMat_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_uMat : (uMat (F := F)).det = 1 := by
  simp [uMat, Matrix.det_fin_two]

theorem uMat_pow_apply_one_zero (i : ℕ) (hi : i % 3 ≠ 0) :
    (uMat (F := F) ^ i) 1 0 = 1 ∨ (uMat (F := F) ^ i) 1 0 = -1 := by
  have h : uMat (F := F) ^ i = uMat ^ (i % 3) := by
    conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, uMat_cube, one_pow, one_mul]
  rw [h]
  have : i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases this with h1 | h1 <;> rw [h1]
  · left
    simp [uMat]
  · right
    rw [uMat_sq]
    simp

@[expose] def xMat (x z : F) : Matrix (Fin 2) (Fin 2) F := !![x, z - x; z, -x]

theorem xMat_mul_uMat (x z : F) : xMat x z * uMat = uMat ^ 2 * xMat x z := by
  rw [uMat_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, xMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_xMat (x z : F) : (xMat x z).det = -(x ^ 2 - x * z + z ^ 2) := by
  simp [xMat, Matrix.det_fin_two]
  ring

@[expose] def xMatAdj (x z : F) : Matrix (Fin 2) (Fin 2) F := !![-x, x - z; -z, x]

theorem xMat_mul_xMatAdj (x z : F) :
    xMat x z * xMatAdj x z = (xMat x z).det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [det_xMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMat, xMatAdj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem xMatAdj_mul_xMat (x z : F) :
    xMatAdj x z * xMat x z = (xMat x z).det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [det_xMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMat, xMatAdj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_sq_sub_mul_add_sq_eq_neg_one {K : Type*} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : ∃ x z : K, x ^ 2 - x * z + z ^ 2 = -1 := by
  classical
  haveI := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have hodd : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  obtain ⟨y, z, hyz⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2 + C (4 : K)) (g := C (3 : K) * X ^ 2)
    (degree_X_pow_add_C (by norm_num) _) (degree_C_mul_X_pow 2 h3) hodd
  refine ⟨(y + z) / 2, z, ?_⟩
  simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at hyz
  field_simp
  linear_combination hyz

end CFSG.RankThree.PartTwo.KFacts.KF430
