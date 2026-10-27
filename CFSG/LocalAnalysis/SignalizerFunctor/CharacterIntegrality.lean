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
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

universe groupUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem finite_order_eigenvalue_pow_eq_one
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    (operator : Module.End ℂ VectorType) (order : ℕ) (finite_order : operator ^ order = 1)
    (eigenvalue : ℂ) (eigen : operator.HasEigenvalue eigenvalue) : eigenvalue ^ order = 1 := by
  obtain ⟨vector, vector_eigen⟩ := eigen.exists_hasEigenvector
  have equal := vector_eigen.pow_apply order
  rw [finite_order] at equal
  have vector_ne : vector ≠ 0 := vector_eigen.2
  have smul_equal : eigenvalue ^ order • vector = (1 : ℂ) • vector := by
    simpa only [one_smul, Module.End.one_apply] using equal.symm
  exact (smul_left_injective ℂ vector_ne) smul_equal

theorem finite_order_operator_trace_integral
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType]
    (operator : Module.End ℂ VectorType) (order : ℕ) (order_positive : 0 < order)
    (finite_order : operator ^ order = 1) : IsIntegral ℤ ((LinearMap.trace ℂ VectorType) operator) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply IsIntegral.multiset_sum
  intro eigenvalue member
  have root := (Polynomial.mem_roots'.mp member).2
  have eigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly operator eigenvalue).mpr root
  have power := finite_order_eigenvalue_pow_eq_one operator order finite_order eigenvalue eigen
  apply IsIntegral.of_pow order_positive
  rw [power]
  exact isIntegral_one

theorem finite_group_character_integral
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType] (representation : Representation ℂ GroupType VectorType)
    (element : GroupType) : IsIntegral ℤ (representation.character element) := by
  have finite_order : representation element ^ orderOf element = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  exact finite_order_operator_trace_integral (representation element) (orderOf element) (orderOf_pos element) finite_order

end CFSG.SignalizerFunctor.Helpers
