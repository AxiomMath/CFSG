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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def dotBilin (n : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)

theorem dotBilin_apply {n : ℕ} (x y : Fin n → ZMod 2) : dotBilin n x y = x ⬝ᵥ y := rfl

theorem dotBilin_isSymm (n : ℕ) : (dotBilin n).IsSymm :=
  ⟨fun x y => by rw [dotBilin_apply, dotBilin_apply, dotProduct_comm]⟩

theorem dotBilin_nondegenerate (n : ℕ) : (dotBilin n).Nondegenerate := by
  have key : ∀ x : Fin n → ZMod 2, (∀ y, x ⬝ᵥ y = 0) → x = 0 := by
    intro x hx
    funext i
    have h := hx (Pi.single i 1)
    simpa using h
  refine ⟨fun x hx => key x hx, fun y hy => key y fun x => ?_⟩
  rw [dotProduct_comm]
  exact hy x

theorem finrank_dotBilin_orthogonal_add (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) ((dotBilin n).orthogonal D) + Module.finrank (ZMod 2) D = n := by
  have h := LinearMap.BilinForm.finrank_orthogonal (dotBilin_nondegenerate n) D
  have hle : Module.finrank (ZMod 2) D ≤ n := by
    simpa using Submodule.finrank_le D
  simp only [Module.finrank_fin_fun] at h
  omega

theorem dotBilin_orthogonal_orthogonal (n : ℕ) (D : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (dotBilin n).orthogonal ((dotBilin n).orthogonal D) = D :=
  LinearMap.BilinForm.orthogonal_orthogonal (dotBilin_nondegenerate n)
    (dotBilin_isSymm n).isRefl D

end CFSG.ASVolI.ChH
