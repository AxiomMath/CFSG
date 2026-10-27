module

public import Mathlib.Algebra.DirectSum.LinearMap
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

universe groupUniverse moduleUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem group_algebra_independent_restrictScalars
    {GroupType : Type groupUniverse} [Monoid GroupType]
    {ModuleType : Type moduleUniverse} [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    {IndexType : Type indexUniverse} (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) ModuleType)
    (independent : iSupIndep summands) : iSupIndep (fun index => (summands index).restrictScalars ℂ) := by
  rw [iSupIndep_def] at independent ⊢
  intro index
  have disjoint := independent index
  rw [disjoint_iff] at disjoint
  rw [disjoint_iff]
  simpa only [Submodule.restrictScalars_inf, Submodule.restrictScalars_iSup, Submodule.restrictScalars_bot]
    using congrArg (Submodule.restrictScalars ℂ) disjoint

theorem group_algebra_internal_restrictScalars
    {GroupType : Type groupUniverse} [Monoid GroupType]
    {ModuleType : Type moduleUniverse} [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    {IndexType : Type indexUniverse} [DecidableEq IndexType]
    (summands : IndexType → Submodule (MonoidAlgebra ℂ GroupType) ModuleType)
    (independent : iSupIndep summands) (spanning : ⨆ index, summands index = ⊤) :
    DirectSum.IsInternal (fun index => (summands index).restrictScalars ℂ) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (group_algebra_independent_restrictScalars summands independent)
  rw [← Submodule.restrictScalars_iSup, spanning, Submodule.restrictScalars_top]

theorem group_algebra_simple_character_decomposition
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Module ℂ ModuleType]
    [Module (MonoidAlgebra ℂ GroupType) ModuleType] [IsScalarTower ℂ (MonoidAlgebra ℂ GroupType) ModuleType]
    [FiniteDimensional ℂ ModuleType] :
    ∃ summands : Set (Submodule (MonoidAlgebra ℂ GroupType) ModuleType), ∃ finite : summands.Finite,
      sSupIndep summands ∧ sSup summands = ⊤ ∧
      (∀ summand ∈ summands, IsSimpleModule (MonoidAlgebra ℂ GroupType) summand) ∧
      (∀ element : GroupType, (Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType).character element =
        ∑ summand ∈ finite.toFinset,
          (Representation.ofModule' (k := ℂ) (G := GroupType) summand).character element) := by
  classical
  let : NeZero (Nat.card GroupType : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  let : Module.Finite (MonoidAlgebra ℂ GroupType) ModuleType :=
    Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ GroupType) ModuleType
  obtain ⟨summands, finite, independent, spanning, simple⟩ :=
    (IsSemisimpleModule.finite_tfae (R := MonoidAlgebra ℂ GroupType) (M := ModuleType)).out 1 5 |>.mp
      (inferInstance : Module.Finite (MonoidAlgebra ℂ GroupType) ModuleType)
  refine ⟨summands, finite, independent, spanning, simple, ?_⟩
  let : Fintype summands := finite.fintype
  let restricted : summands → Submodule ℂ ModuleType := fun summand => summand.val.restrictScalars ℂ
  have internal : DirectSum.IsInternal restricted := by
    apply group_algebra_internal_restrictScalars (fun summand : summands => summand.val)
      ((sSupIndep_iff summands).mp independent)
    rw [iSup_subtype]
    rwa [sSup_eq_iSup] at spanning
  intro element
  have invariant : ∀ summand : summands,
      Set.MapsTo ((Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType) element)
        (restricted summand) (restricted summand) := by
    intro summand vector member
    exact summand.val.smul_mem (MonoidAlgebra.of ℂ GroupType element) member
  have trace_sum := LinearMap.trace_eq_sum_trace_restrict internal invariant
  have summand_trace : ∀ summand : summands,
      (LinearMap.trace ℂ (restricted summand))
          (((Representation.ofModule' (k := ℂ) (G := GroupType) ModuleType) element).restrict (invariant summand)) =
        (Representation.ofModule' (k := ℂ) (G := GroupType) summand.val).character element := by
    intro summand
    rfl
  change (LinearMap.trace ℂ ModuleType) _ = _
  rw [trace_sum]
  calc
    _ = ∑ summand : summands,
        (Representation.ofModule' (k := ℂ) (G := GroupType) summand.val).character element :=
      Finset.sum_congr rfl (fun summand _member => summand_trace summand)
    _ = _ := (Finset.sum_subtype finite.toFinset (fun _summand => Set.Finite.mem_toFinset finite)
      (fun summand : Submodule (MonoidAlgebra ℂ GroupType) ModuleType =>
        (Representation.ofModule' (k := ℂ) (G := GroupType) summand).character element)).symm

end CFSG.SignalizerFunctor.Helpers
