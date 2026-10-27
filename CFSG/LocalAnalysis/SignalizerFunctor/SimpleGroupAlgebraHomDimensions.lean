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
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
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

universe groupUniverse moduleUniverse targetUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem simple_group_algebra_end_finrank
    {GroupType : Type groupUniverse} [Monoid GroupType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    [FiniteDimensional ℂ ModuleType] [IsSimpleModule (MonoidAlgebra ℂ GroupType) ModuleType] :
    Module.finrank ℂ (Module.End (MonoidAlgebra ℂ GroupType) ModuleType) = 1 := by
  have bijective := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed ℂ
    (A := MonoidAlgebra ℂ GroupType) (V := ModuleType)
  have equal := (LinearEquiv.ofBijective
    (Algebra.linearMap ℂ (Module.End (MonoidAlgebra ℂ GroupType) ModuleType)) bijective).finrank_eq
  rw [Module.finrank_self] at equal
  exact equal.symm

theorem simple_group_algebra_hom_finrank
    {GroupType : Type groupUniverse} [Monoid GroupType]
    (SourceType : Type moduleUniverse) [AddCommGroup SourceType] [Module ℂ SourceType]
    [Module (MonoidAlgebra ℂ GroupType) SourceType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) SourceType]
    [FiniteDimensional ℂ SourceType] [IsSimpleModule (MonoidAlgebra ℂ GroupType) SourceType]
    (TargetType : Type targetUniverse) [AddCommGroup TargetType] [Module ℂ TargetType]
    [Module (MonoidAlgebra ℂ GroupType) TargetType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) TargetType]
    [FiniteDimensional ℂ TargetType] [IsSimpleModule (MonoidAlgebra ℂ GroupType) TargetType] :
    Module.finrank ℂ (SourceType →ₗ[MonoidAlgebra ℂ GroupType] TargetType) =
      @ite ℕ (Nonempty (SourceType ≃ₗ[MonoidAlgebra ℂ GroupType] TargetType)) (Classical.propDecidable _) 1 0 := by
  classical
  split_ifs with equivalent
  · obtain ⟨equivalence⟩ := equivalent
    rw [(LinearEquiv.congrLeft TargetType ℂ equivalence).finrank_eq]
    exact simple_group_algebra_end_finrank (GroupType := GroupType) TargetType
  · have all_zero : ∀ hom : SourceType →ₗ[MonoidAlgebra ℂ GroupType] TargetType, hom = 0 := by
      intro hom
      rcases hom.bijective_or_eq_zero with bijective | zero
      · exact False.elim (equivalent ⟨LinearEquiv.ofBijective hom bijective⟩)
      · exact zero
    let : Subsingleton (SourceType →ₗ[MonoidAlgebra ℂ GroupType] TargetType) :=
      ⟨fun first second => (all_zero first).trans (all_zero second).symm⟩
    exact Module.finrank_zero_of_subsingleton

theorem group_algebra_hom_finrank_decomposition
    {GroupType : Type groupUniverse} [Monoid GroupType]
    {ModuleType : Type moduleUniverse} [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    {IndexType : Type indexUniverse} [Fintype IndexType] [DecidableEq IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) ModuleType)
    (internal : DirectSum.IsInternal summands)
    (TargetType : Type targetUniverse) [AddCommGroup TargetType] [Module ℂ TargetType]
    [Module (MonoidAlgebra ℂ GroupType) TargetType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) TargetType]
    [∀ index, FiniteDimensional ℂ ((summands index) →ₗ[MonoidAlgebra ℂ GroupType] TargetType)] :
    Module.finrank ℂ (ModuleType →ₗ[MonoidAlgebra ℂ GroupType] TargetType) =
      ∑ index, Module.finrank ℂ ((summands index) →ₗ[MonoidAlgebra ℂ GroupType] TargetType) := by
  let decomposition : ModuleType ≃ₗ[MonoidAlgebra ℂ GroupType] (index : IndexType) → summands index :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap summands) internal).symm.trans
      (DFinsupp.linearEquivFunOnFintype (R := MonoidAlgebra ℂ GroupType))
  rw [(LinearEquiv.congrLeft TargetType ℂ decomposition).finrank_eq,
    ← (LinearMap.lsum (MonoidAlgebra ℂ GroupType) (fun index => summands index) ℂ).finrank_eq,
    Module.finrank_pi_fintype]

end CFSG.SignalizerFunctor.Helpers
