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

namespace CFSG.Quasithin.RonanH43

open Matrix

theorem inv_eq_trv :
    ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M * M = 1 → M ≠ 1 →
      ∃ c φ : Fin 3 → ZMod 2, c ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ c = 0 ∧ M = 1 + vecMulVec c φ := by
  decide +kernel

theorem symm_mulVec_eq :
    ∀ c φ : Fin 3 → ZMod 2, c ≠ 0 → φ ≠ 0 → φ ⬝ᵥ c = 0 →
    ∀ H : Matrix (Fin 3) (Fin 3) (ZMod 2), Hᵀ = H → (∀ v, H *ᵥ v = 0 → v = 0) →
      (1 + vecMulVec φ c) * H = H * (1 + vecMulVec c φ) → H *ᵥ c = φ := by
  decide +kernel

theorem exists_mulVec_eq_single :
    ∀ c : Fin 3 → ZMod 2, c ≠ 0 →
      ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2), (∀ v, M *ᵥ v = 0 → v = 0) ∧
        M *ᵥ c = Pi.single 0 1 := by
  decide +kernel

end CFSG.Quasithin.RonanH43
