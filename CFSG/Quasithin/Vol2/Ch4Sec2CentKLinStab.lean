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

namespace CFSG.Quasithin.H13.Ch4.CentK

open Matrix

variable {F : Type} [Field F]

def stabVec (w : Fin 3 → F) : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have ha' : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := ha
    have hb' : (b : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := hb
    have e := Matrix.SpecialLinearGroup.coe_mul a b
    show ((a * b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w
    rw [e, ← mulVec_mulVec, hb', ha']
  inv_mem' := fun {a} ha => by
    have ha' : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := ha
    have e := Matrix.SpecialLinearGroup.coe_inv a
    have d := Matrix.SpecialLinearGroup.det_coe a
    show ((a⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w
    rw [e]
    calc (a : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ w
        = (a : Matrix (Fin 3) (Fin 3) F).adjugate *ᵥ ((a : Matrix (Fin 3) (Fin 3) F) *ᵥ w) := by
          rw [ha']
      _ = w := by
          rw [mulVec_mulVec, adjugate_mul, d, one_smul, one_mulVec]

theorem mem_stabVec {w : Fin 3 → F} {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ stabVec w ↔ (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := Iff.rfl

end CFSG.Quasithin.H13.Ch4.CentK
