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
public import Mathlib.RepresentationTheory.Irreducible
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

universe groupUniverse moduleUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem ofModule_algebra_action
    {GroupType : Type groupUniverse} [Monoid GroupType]
    {ModuleType : Type moduleUniverse} [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    (element : MonoidAlgebra ℂ GroupType) (vector : ModuleType) :
    ((Representation.ofModule' ModuleType).asAlgebraHom element) vector = element • vector := by
  induction element using MonoidAlgebra.induction_on with
  | of groupElement => rw [Representation.asAlgebraHom_of]; rfl
  | add first second first_equal second_equal =>
      simpa only [map_add, LinearMap.add_apply, add_smul] using congrArg₂ (· + ·) first_equal second_equal
  | smul scalar element equal =>
      simpa only [map_smul, LinearMap.smul_apply, smul_assoc] using congrArg (scalar • ·) equal

noncomputable def ofModuleAsModuleEquiv
    {GroupType : Type groupUniverse} [Monoid GroupType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType] :
    (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).asModule ≃ₗ[MonoidAlgebra ℂ GroupType] ModuleType :=
  { (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).asModuleEquiv.toAddEquiv with
    map_smul' := fun scalar vector => by
      change (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).asModuleEquiv (scalar • vector) =
        scalar • (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).asModuleEquiv vector
      rw [Representation.asModuleEquiv_map_smul, ofModule_algebra_action] }

theorem simple_group_algebra_module_irreducible
    {GroupType : Type groupUniverse} [Monoid GroupType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    [IsSimpleModule (MonoidAlgebra ℂ GroupType) ModuleType] :
    (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).IsIrreducible := by
  let : IsSimpleModule (MonoidAlgebra ℂ GroupType) (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).asModule :=
    (ofModuleAsModuleEquiv (GroupType := GroupType) ModuleType).isSimpleModule_iff.mpr inferInstance
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso
    (ρ := Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType)).isSimpleOrder

end CFSG.SignalizerFunctor.Helpers
