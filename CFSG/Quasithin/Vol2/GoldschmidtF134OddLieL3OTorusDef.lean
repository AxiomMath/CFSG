module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
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

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def diagMat (a b : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![(a : K), (b : K), (((a * b)⁻¹ : Kˣ) : K)]

theorem det_diagMat (a b : Kˣ) : (diagMat a b).det = 1 := by
  rw [diagMat, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem diagMat_mul (a b a' b' : Kˣ) :
    diagMat a b * diagMat a' b' = diagMat (a * a') (b * b') := by
  rw [diagMat, diagMat, diagMat, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i
  · simp
  · simp
  · simp
    ring

theorem diagMat_one : diagMat (1 : Kˣ) (1 : Kˣ) = (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [diagMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def diagHom : Kˣ × Kˣ →* SL(3, K) where
  toFun x := ⟨diagMat x.1 x.2, det_diagMat x.1 x.2⟩
  map_one' := Subtype.ext diagMat_one
  map_mul' x y := Subtype.ext (diagMat_mul x.1 x.2 y.1 y.2).symm

@[simp]
theorem coe_diagHom (x : Kˣ × Kˣ) :
    ((diagHom x : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = diagMat x.1 x.2 :=
  rfl

@[expose] def torusSL (K : Type) [Field K] (p : ℕ) : Subgroup SL(3, K) :=
  ((rootsOfUnity p K).prod (rootsOfUnity p K)).map diagHom

@[expose] def torusP (K : Type) [Field K] (p : ℕ) : Subgroup (projectiveSL 3 K) :=
  (torusSL K p).map (proj 3 K)

end CFSG.Quasithin.H13.NQCore.L3Odd
