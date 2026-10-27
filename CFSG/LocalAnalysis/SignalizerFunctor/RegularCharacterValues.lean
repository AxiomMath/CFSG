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

universe groupUniverse moduleUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem group_algebra_regular_representation
    {GroupType : Type groupUniverse} [Group GroupType] :
    Representation.ofModule' (k := ℂ) (G := GroupType) (MonoidAlgebra ℂ GroupType) =
      Representation.leftRegular ℂ GroupType := by
  apply MonoidHom.ext
  intro element
  apply LinearMap.ext
  intro vector
  change MonoidAlgebra.of ℂ GroupType element * vector = _
  rw [← Representation.asAlgebraHom_of,
    Representation.asAlgebraHom_ofMulAction_smul_eq_mul]

theorem finite_group_regular_character
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (element : GroupType) :
    (Representation.leftRegular ℂ GroupType).character element =
      @ite ℂ (element = 1) (Classical.propDecidable _) (Nat.card GroupType : ℂ) 0 := by
  classical
  let : Fintype GroupType := Fintype.ofFinite GroupType
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis GroupType ℂ)]
  unfold Matrix.trace
  have diagonal : ∀ selected : GroupType,
      (LinearMap.toMatrix (MonoidAlgebra.basis GroupType ℂ) (MonoidAlgebra.basis GroupType ℂ)
        ((Representation.leftRegular ℂ GroupType) element)) selected selected =
        if element = 1 then (1 : ℂ) else 0 := by
    intro selected
    rw [LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, Representation.ofMulAction_single]
    change ((MonoidAlgebra.basis GroupType ℂ).repr (MonoidAlgebra.single (element * selected) 1)) selected = _
    rw [← MonoidAlgebra.basis_apply, Module.Basis.repr_self_apply]
    simp only [mul_eq_right]
  simp only [Matrix.diag_apply, diagonal]
  split_ifs with equal
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  · simp only [Finset.sum_const_zero]

theorem group_algebra_regular_hom_finrank
    {GroupType : Type groupUniverse} [Monoid GroupType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType] :
    Module.finrank ℂ ((MonoidAlgebra ℂ GroupType) →ₗ[MonoidAlgebra ℂ GroupType] ModuleType) =
      Module.finrank ℂ ModuleType :=
  (LinearMap.ringLmapEquivSelf (MonoidAlgebra ℂ GroupType) ℂ ModuleType).finrank_eq

theorem equivalent_group_algebra_characters
    {GroupType : Type groupUniverse} [Group GroupType]
    {SourceType : Type moduleUniverse} [AddCommGroup SourceType] [Module ℂ SourceType]
    [Module (MonoidAlgebra ℂ GroupType) SourceType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) SourceType]
    {TargetType : Type moduleUniverse} [AddCommGroup TargetType] [Module ℂ TargetType]
    [Module (MonoidAlgebra ℂ GroupType) TargetType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) TargetType]
    (equivalence : SourceType ≃ₗ[MonoidAlgebra ℂ GroupType] TargetType) (element : GroupType) :
    (Representation.ofModule' (k := ℂ) (G := GroupType) SourceType).character element =
      (Representation.ofModule' (k := ℂ) (G := GroupType) TargetType).character element := by
  let complex_equivalence := equivalence.restrictScalars ℂ
  have operator_equal : complex_equivalence.conj
      ((Representation.ofModule' (k := ℂ) (G := GroupType) SourceType) element) =
      (Representation.ofModule' (k := ℂ) (G := GroupType) TargetType) element := by
    ext vector
    change equivalence ((MonoidAlgebra.of ℂ GroupType element) • equivalence.symm vector) =
      (MonoidAlgebra.of ℂ GroupType element) • vector
    rw [map_smul, equivalence.apply_symm_apply]
  unfold Representation.character
  rw [← operator_equal, LinearMap.trace_conj']

end CFSG.SignalizerFunctor.Helpers
