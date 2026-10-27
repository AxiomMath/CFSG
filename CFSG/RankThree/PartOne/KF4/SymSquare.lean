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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.RankThree.PartOne.KF4

open Matrix

variable {K : Type} [Field K]

@[expose] def symCoord (X : Matrix (Fin 3) (Fin 3) K) : Fin 6 → K :=
  ![X 2 2, -X 1 2, X 0 2, X 1 1, -X 0 1, X 0 0]

@[expose] def symMat (x : Fin 6 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![x 5, -x 4, x 2; -x 4, x 3, -x 1; x 2, -x 1, x 0]

@[expose] def symCong (B : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun i j => symCoord (B * symMat (Pi.single j 1) * Bᵀ) i

theorem symCong_one : symCong (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symCong, symCoord, symMat, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply]

theorem symCoord_symMat (x : Fin 6 → K) : symCoord (symMat x) = x := by
  ext i
  fin_cases i <;> simp [symCoord, symMat]

theorem symMat_transpose (x : Fin 6 → K) : (symMat x)ᵀ = symMat x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat]

theorem symMat_symCoord {X : Matrix (Fin 3) (Fin 3) K} (hX : Xᵀ = X) :
    symMat (symCoord X) = X := by
  have h10 : X 1 0 = X 0 1 := by simpa using congrFun (congrFun hX 0) 1
  have h20 : X 2 0 = X 0 2 := by simpa using congrFun (congrFun hX 0) 2
  have h21 : X 2 1 = X 1 2 := by simpa using congrFun (congrFun hX 1) 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMat, symCoord, h10, h20, h21]

theorem symCong_mulVec (B : Matrix (Fin 3) (Fin 3) K) (x : Fin 6 → K) :
    symCong B *ᵥ x = symCoord (B * symMat x * Bᵀ) := by
  ext i
  fin_cases i <;>
    simp [symCong, symCoord, symMat, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_three, Fin.sum_univ_six, Pi.single_apply, Matrix.transpose_apply] <;> ring

theorem symCong_mul (B₁ B₂ : Matrix (Fin 3) (Fin 3) K) :
    symCong (B₁ * B₂) = symCong B₁ * symCong B₂ := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [symCong_mulVec, ← Matrix.mulVec_mulVec, symCong_mulVec, symCong_mulVec]
  have hsym : (B₂ * symMat (Pi.single j 1) * B₂ᵀ)ᵀ = B₂ * symMat (Pi.single j 1) * B₂ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, symMat_transpose, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [symMat_symCoord hsym, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem eq_one_of_symCong_eq_one {A : Matrix (Fin 3) (Fin 3) K} (h : symCong A = 1)
    (hdet : A.det = 1) : A = 1 := by
  have e : ∀ i j, symCong A i j = (1 : Matrix (Fin 6) (Fin 6) K) i j := fun i j => by rw [h]
  have c00 := e 0 0
  have c30 := e 3 0
  have c50 := e 5 0
  have c55 := e 5 5
  have c35 := e 3 5
  have c05 := e 0 5
  have c33 := e 3 3
  have c53 := e 5 3
  have c03 := e 0 3
  have c44 := e 4 4
  have c11 := e 1 1
  have c22 := e 2 2
  simp [symCong, symCoord, symMat, Matrix.mul_apply, Fin.sum_univ_three, Pi.single_apply,
    Matrix.transpose_apply] at c00 c30 c50 c55 c35 c05 c33 c53 c03 c44 c11 c22
  rw [Matrix.det_fin_three] at hdet
  simp only [c30, c50, c35, c05, c53, c03] at hdet c44 c11 c22
  simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hdet c44 c11 c22
  have h11 : A 1 1 = A 0 0 := by
    calc A 1 1 = A 1 1 * (A 0 0 * A 0 0) := by rw [c55, mul_one]
      _ = A 0 0 * (A 0 0 * A 1 1) := by ring
      _ = A 0 0 := by rw [c44, mul_one]
  have h22 : A 2 2 = A 0 0 := by
    calc A 2 2 = A 2 2 * (A 0 0 * A 0 0) := by rw [c55, mul_one]
      _ = A 0 0 * (A 0 0 * A 2 2) := by ring
      _ = A 0 0 := by rw [c22, mul_one]
  have h00 : A 0 0 = 1 := by
    have h3 : A 0 0 * A 0 0 * A 0 0 = 1 := by
      rw [h11, h22] at hdet
      linear_combination hdet
    calc A 0 0 = A 0 0 * (A 0 0 * A 0 0) := by rw [c55, mul_one]
      _ = 1 := by rw [← mul_assoc]; exact h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h22, c30, c50, c35, c05, c53, c03]

theorem symCong_diagonal (d : Fin 3 → K) :
    symCong (Matrix.diagonal d) = Matrix.diagonal
      ![d 2 * d 2, d 1 * d 2, d 0 * d 2, d 1 * d 1, d 0 * d 1, d 0 * d 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symCong, symCoord, symMat, Matrix.mul_apply, Pi.single_apply, Matrix.diagonal_apply]

end CFSG.RankThree.PartOne.KF4
