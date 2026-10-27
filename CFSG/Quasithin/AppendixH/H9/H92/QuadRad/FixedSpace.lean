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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

@[expose] def matFixSpace (n : ℕ) (E : Subgroup (GL (Fin n) (ZMod 2))) :
    Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {x | ∀ g ∈ E, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x}
  add_mem' := by
    intro x y hx hy g hg
    rw [Matrix.mulVec_add, hx g hg, hy g hg]
  zero_mem' := by
    intro g _
    rw [Matrix.mulVec_zero]
  smul_mem' := by
    intro c x hx g hg
    rw [Matrix.mulVec_smul, hx g hg]

@[expose] def matMoveSpace (n : ℕ) (E : Subgroup (GL (Fin n) (ZMod 2))) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2)
    {y | ∃ g ∈ E, ∃ x : Fin n → ZMod 2,
      y = ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x}

theorem mem_matFixSpace {n : ℕ} {E : Subgroup (GL (Fin n) (ZMod 2))} {x : Fin n → ZMod 2} :
    x ∈ matFixSpace n E ↔ ∀ g ∈ E, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x := Iff.rfl

theorem sub_one_mulVec_eq_zero_of_mem_matFixSpace {n : ℕ} {E : Subgroup (GL (Fin n) (ZMod 2))}
    {g : GL (Fin n) (ZMod 2)} (hg : g ∈ E) {u : Fin n → ZMod 2} (hu : u ∈ matFixSpace n E) :
    ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ u = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hu g hg, sub_self]

theorem sub_one_mulVec_mem_matMoveSpace {n : ℕ} {E : Subgroup (GL (Fin n) (ZMod 2))}
    {g : GL (Fin n) (ZMod 2)} (hg : g ∈ E) (x : Fin n → ZMod 2) :
    ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x ∈ matMoveSpace n E :=
  Submodule.subset_span ⟨g, hg, x, rfl⟩

theorem matMoveSpace_le_matFixSpace {n : ℕ} {E : Subgroup (GL (Fin n) (ZMod 2))}
    (hq : ∀ g ∈ E, ∀ h ∈ E, ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *
      ((h : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) = 0) :
    matMoveSpace n E ≤ matFixSpace n E := by
  refine Submodule.span_le.mpr ?_
  rintro y ⟨h, hh, x, rfl⟩ g hg
  have h0 : ((g : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ
      (((h : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, hq g hg h hh, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

end CFSG.ASVolI.ChH
