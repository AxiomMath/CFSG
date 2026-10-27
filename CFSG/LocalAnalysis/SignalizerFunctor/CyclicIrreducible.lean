module

public import CFSG.Mathlib.GroupTheory.Basic
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

universe ringUniverse moduleUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem domain_of_faithful_simple_module (RingType : Type ringUniverse)
    (ModuleType : Type moduleUniverse) [CommRing RingType] [AddCommGroup ModuleType]
    [Module RingType ModuleType] [FaithfulSMul RingType ModuleType]
    [IsSimpleModule RingType ModuleType] : IsDomain RingType := by
  have annihilator_bot : Module.annihilator RingType ModuleType = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  have maximal : (⊥ : Ideal RingType).IsMaximal :=
    annihilator_bot ▸ IsSimpleModule.annihilator_isMaximal
  let : (⊥ : Ideal RingType).IsPrime := maximal.isPrime
  exact IsDomain.of_bot_isPrime RingType

theorem cyclic_of_faithful_simple_module (RingType : Type ringUniverse)
    (ModuleType : Type moduleUniverse) [CommRing RingType] [AddCommGroup ModuleType]
    [Module RingType ModuleType] [FaithfulSMul RingType ModuleType]
    [IsSimpleModule RingType ModuleType]
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (homomorphism : GroupType →* RingType) (injective : Function.Injective homomorphism) :
    IsCyclic GroupType := by
  let := domain_of_faithful_simple_module RingType ModuleType
  exact isCyclic_of_injective_ringHom homomorphism injective

theorem cyclic_of_irreducible_commuting_endomorphisms
    (ScalarType : Type ringUniverse) [Ring ScalarType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Nontrivial ModuleType]
    [Module ScalarType ModuleType]
    {GroupType : Type groupUniverse} [CommGroup GroupType] [Finite GroupType]
    (homomorphism : GroupType →* Module.End ScalarType ModuleType)
    (injective : Function.Injective homomorphism)
    (irreducible : ∀ subgroup : AddSubgroup ModuleType,
      (∀ actorElement : GroupType, ∀ element ∈ subgroup,
        homomorphism actorElement element ∈ subgroup) →
      subgroup = ⊥ ∨ subgroup = ⊤) :
    IsCyclic GroupType := by
  let generated : Subring (Module.End ScalarType ModuleType) :=
    Subring.closure (Set.range homomorphism)
  have commuting : IsMulCommutative generated := by
    apply CFSG.subring_isMulCommutative_closure
    rintro first ⟨firstActor, rfl⟩ second ⟨secondActor, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  let := commuting
  let _commRing : CommRing generated :=
    { generated.toRing with mul_comm := mul_comm' }
  let _action : Module generated ModuleType := Module.compHom ModuleType generated.subtype
  have faithful : FaithfulSMul generated ModuleType := by
    constructor
    intro first second equal_actions
    apply Subtype.ext
    apply LinearMap.ext
    exact equal_actions
  let := faithful
  have simple_order : IsSimpleOrder (Submodule generated ModuleType) := by
    constructor
    intro submodule
    have invariant : ∀ actorElement : GroupType, ∀ element ∈ submodule.toAddSubgroup,
        homomorphism actorElement element ∈ submodule.toAddSubgroup := by
      intro actorElement element member
      exact submodule.smul_mem
        (⟨homomorphism actorElement, Subring.subset_closure ⟨actorElement, rfl⟩⟩ : generated)
        member
    rcases irreducible submodule.toAddSubgroup invariant with trivial | whole
    · left
      apply (Submodule.toAddSubgroup_inj _ _).mp
      exact trivial
    · right
      apply (Submodule.toAddSubgroup_inj _ _).mp
      exact whole
  let := simple_order
  let : IsSimpleModule generated ModuleType := ⟨⟩
  let restricted : GroupType →* generated := homomorphism.codRestrict generated
    (fun actorElement => Subring.subset_closure ⟨actorElement, rfl⟩)
  apply cyclic_of_faithful_simple_module generated ModuleType restricted
  intro first second equal_images
  exact injective (congrArg (fun element : generated =>
    (element : Module.End ScalarType ModuleType)) equal_images)

end CFSG.SignalizerFunctor.Helpers
