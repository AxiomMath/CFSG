module

public import CFSG.LocalAnalysis.SignalizerFunctor.CyclicIrreducible
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Order.Hom.Esakia

public section

universe actorUniverse moduleUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem cyclic_image_of_irreducible_additive_action
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType] [Nontrivial ModuleType]
    [DistribMulAction ActorType ModuleType]
    (irreducible : ∀ subgroup : AddSubgroup ModuleType,
      (∀ actorElement : ActorType, ∀ element ∈ subgroup,
        actorElement • element ∈ subgroup) →
      subgroup = ⊥ ∨ subgroup = ⊤) :
    IsCyclic (DistribMulAction.toModuleEnd ℤ (S := ActorType) ModuleType).toHomUnits.range := by
  let representation := DistribMulAction.toModuleEnd ℤ (S := ActorType) ModuleType
  let unitRepresentation := representation.toHomUnits
  let image := unitRepresentation.range
  have image_commuting : IsMulCommutative image := by
    apply isMulCommutative_iff.mpr
    intro first second
    apply Subtype.ext
    change (first : (Module.End ℤ ModuleType)ˣ) * second =
      (second : (Module.End ℤ ModuleType)ˣ) * first
    obtain ⟨firstActor, first_maps⟩ := first.property
    obtain ⟨secondActor, second_maps⟩ := second.property
    rw [← first_maps, ← second_maps, ← map_mul, ← map_mul, mul_comm]
  let _commGroup : CommGroup image :=
    { image.toGroup with mul_comm := isMulCommutative_iff.mp image_commuting }
  let _finite : Finite image :=
    Finite.of_surjective unitRepresentation.rangeRestrict
      unitRepresentation.rangeRestrict_surjective
  let inclusion : image →* Module.End ℤ ModuleType :=
    (Units.coeHom (Module.End ℤ ModuleType)).comp image.subtype
  apply cyclic_of_irreducible_commuting_endomorphisms ℤ ModuleType inclusion
  · intro first second same
    apply Subtype.ext
    apply Units.ext
    exact same
  · intro subgroup invariant
    apply irreducible subgroup
    intro actorElement element member
    exact invariant (unitRepresentation.rangeRestrict actorElement) element member

abbrev additiveActionOfMultiplicative
    (ActorType : Type actorUniverse) [Group ActorType]
    (GroupType : Type groupUniverse) [CommGroup GroupType]
    [MulDistribMulAction ActorType GroupType] :
    DistribMulAction ActorType (Additive GroupType) where
  smul actorElement element := Additive.ofMul (actorElement • element.toMul)
  one_smul element := one_smul ActorType element.toMul
  mul_smul first second element := mul_smul first second element.toMul
  smul_zero actorElement := by
    change actorElement • (1 : GroupType) = 1
    exact smul_one actorElement
  smul_add actorElement first second := by
    change actorElement • (first.toMul * second.toMul) =
      actorElement • first.toMul * actorElement • second.toMul
    exact MulDistribMulAction.smul_mul actorElement first.toMul second.toMul

theorem cyclic_quotient_fixing_irreducible_abelian_group
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (GroupType : Type groupUniverse) [CommGroup GroupType] [Nontrivial GroupType]
    [MulDistribMulAction ActorType GroupType]
    (irreducible : ∀ subgroup : Subgroup GroupType,
      (∀ actorElement : ActorType, ∀ element ∈ subgroup,
        actorElement • element ∈ subgroup) →
      subgroup = ⊥ ∨ subgroup = ⊤) :
    ∃ kernel : Subgroup ActorType, IsCyclic (ActorType ⧸ kernel) ∧
      FixedPoints.subgroup kernel GroupType = ⊤ := by
  let _additiveAction := additiveActionOfMultiplicative ActorType GroupType
  let representation := DistribMulAction.toModuleEnd ℤ (S := ActorType) (Additive GroupType)
  let unitRepresentation := representation.toHomUnits
  have additive_irreducible : ∀ subgroup : AddSubgroup (Additive GroupType),
      (∀ actorElement : ActorType, ∀ element ∈ subgroup,
        actorElement • element ∈ subgroup) →
      subgroup = ⊥ ∨ subgroup = ⊤ := by
    intro subgroup invariant
    have subgroup_invariant : ∀ actorElement : ActorType,
        ∀ element ∈ subgroup.toSubgroup',
          actorElement • element ∈ subgroup.toSubgroup' := invariant
    rcases irreducible subgroup.toSubgroup' subgroup_invariant with trivial | whole
    · left
      exact AddSubgroup.toSubgroup'.injective (by simpa using trivial)
    · right
      exact AddSubgroup.toSubgroup'.injective (by simpa using whole)
  let : IsCyclic unitRepresentation.range :=
    cyclic_image_of_irreducible_additive_action ActorType (Additive GroupType)
      additive_irreducible
  refine ⟨unitRepresentation.ker, ?_, ?_⟩
  · exact isCyclic_of_injective
      (QuotientGroup.quotientKerEquivRange unitRepresentation).toMonoidHom
      (QuotientGroup.quotientKerEquivRange unitRepresentation).injective
  · apply top_unique
    intro element _ actorElement
    have trivial_action : representation actorElement.val = 1 :=
      congrArg (fun unit : (Module.End ℤ (Additive GroupType))ˣ =>
        (unit : Module.End ℤ (Additive GroupType))) actorElement.property
    exact congrArg (fun endomorphism : Module.End ℤ (Additive GroupType) =>
      (endomorphism (Additive.ofMul element)).toMul) trivial_action

end CFSG.SignalizerFunctor.Helpers
