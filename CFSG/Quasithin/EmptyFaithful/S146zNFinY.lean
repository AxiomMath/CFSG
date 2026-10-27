module

public import CFSG.Quasithin.EmptyFaithful.S146yA6Mod
public import CFSG.Quasithin.EmptyFaithful.S146zNFinG
public import CFSG.Quasithin.EmptyFaithful.S146zNFinK
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

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

set_option maxRecDepth 100000 in
theorem conj_chain1 : ∃ r : Perm (Fin 6), sign r = 1 ∧ r * bx * r⁻¹ = x0P ∧ r * u1 * r⁻¹ = u1 := by
  unfold bx u1 x0P
  decide +kernel

set_option maxRecDepth 100000 in
theorem conj_chain2 : ∃ r : Perm (Fin 6), sign r = 1 ∧ r * bx * r⁻¹ = u1 ∧
    r * u3 * r⁻¹ = y0P * x0P * y0P⁻¹ := by
  unfold bx u1 u3 x0P y0P
  decide +kernel

set_option maxRecDepth 100000 in
theorem prod_facts : bx * u2 = u1 ∧ bx * u4 = u3 ∧ bx * u2 = u2 * bx ∧ bx * u4 = u4 * bx ∧
    bx ≠ u2 ∧ bx ≠ u4 ∧ bx ≠ 1 ∧ u2 ≠ 1 ∧ u4 ≠ 1 ∧ u2 * u2 = 1 ∧ u4 * u4 = 1 := by
  unfold bx u1 u2 u3 u4
  decide +kernel

end CFSG.Quasithin.A6Fin
