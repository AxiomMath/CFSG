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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open Matrix

variable {F : Type*} [Field F]

theorem det_eq_of_flag (g : Matrix (Fin 3) (Fin 3) F) {u₀ u₁ x : Fin 3 → F}
    (hli : LinearIndependent F ![u₀, u₁, x]) {α₀ α₁ α₃ c₀ c₁ : F}
    (h0 : g.mulVec u₀ = α₀ • u₀) (h1 : g.mulVec u₁ = α₁ • u₁)
    (h3 : g.mulVec x = α₃ • x + c₀ • u₀ + c₁ • u₁) : g.det = α₀ * α₁ * α₃ := by
  let S : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![u₀, u₁, x] j i
  have hS : IsUnit S := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hli using 1
    ext j i
    fin_cases j <;> rfl
  let R : Matrix (Fin 3) (Fin 3) F := !![α₀, 0, c₀; 0, α₁, c₁; 0, 0, α₃]
  have hgS : g * S = S * R := by
    ext i j
    have e0 := congrFun h0 i
    have e1 := congrFun h1 i
    have e3 := congrFun h3 i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul,
      Pi.add_apply] at e0 e1 e3
    fin_cases j
    · simp [S, R, Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination e0
    · simp [S, R, Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination e1
    · simp [S, R, Matrix.mul_apply, Fin.sum_univ_three]
      linear_combination e3
  have hdet : g.det * S.det = S.det * R.det := by rw [← Matrix.det_mul, hgS, Matrix.det_mul]
  have hSd : S.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero
  have hR : R.det = α₀ * α₁ * α₃ := by simp [R, Matrix.det_fin_three]
  rw [← hR]
  exact mul_left_cancel₀ hSd (by rw [mul_comm, hdet])

theorem eq_one_of_flag [CharP F 2] (g : Matrix (Fin 3) (Fin 3) F) (hdet : g.det = 1)
    {u₀ u₁ x : Fin 3 → F} (hli : LinearIndependent F ![u₀, u₁, x]) {α₀ α₁ α₃ c₀ c₁ : F}
    (h0 : g.mulVec u₀ = α₀ • u₀) (h1 : g.mulVec u₁ = α₁ • u₁)
    (h3 : g.mulVec x = α₃ • x + c₀ • u₀ + c₁ • u₁) (hsq0 : α₀ ^ 2 = α₃)
    (hsq1 : α₁ ^ 2 = α₃) : α₀ = 1 := by
  have hd := det_eq_of_flag g hli h0 h1 h3
  have h01 : α₀ = α₁ := CharTwo.sq_inj.mp (hsq0.trans hsq1.symm)
  have h4 : (α₀ ^ 2) ^ 2 = 1 ^ 2 := by
    rw [one_pow, ← hdet, hd, ← h01, ← hsq0]
    ring
  have h2 : α₀ ^ 2 = 1 ^ 2 := by
    rw [CharTwo.sq_inj.mp h4, one_pow]
  exact CharTwo.sq_inj.mp h2

end CFSG.Quasithin.Vol2.Ch11.SecH
