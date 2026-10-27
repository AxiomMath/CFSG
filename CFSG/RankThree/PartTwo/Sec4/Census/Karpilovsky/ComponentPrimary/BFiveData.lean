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

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BScal

@[expose] def fiveM : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 1, 4, 1; 4, 0, 0, 2; 1, 0, 0, 1; 4, 3, 4, 0]

@[expose] def fiveMinv : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 3, 4, 0; 2, 0, 3, 3; 1, 2, 0, 3; 0, 2, 2, 0]

@[expose] def fiveSm : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 2, 2, 4, 2; 1, 4, 4, 0]

@[expose] def fiveCs : Fin 4 → ℕ := ![0, 0, 0, 1]

@[expose] def fiveCt : Fin 4 → ℕ := ![4, 0, 1, 1]

theorem fiveM_mul_inv : fiveM * fiveMinv = 1 := by decide +kernel

theorem fiveSm_ne_one : fiveSm ≠ 1 := by decide +kernel

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.BScal

end
