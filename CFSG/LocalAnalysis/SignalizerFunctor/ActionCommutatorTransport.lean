module

public import CFSG.LocalAnalysis.SignalizerFunctor.IteratedActionCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutatorImages

public section

universe actorUniverse groupUniverse imageUniverse secondActorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction ActorType ImageType]

theorem invariant_action_commutator_le_global (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    invariantActionCommutator parent invariant ≤ actionCommutator (ActorType := ActorType) := by
  let _action := invariantSubgroupAction parent invariant
  exact action_commutator_map_le parent.subtype (fun _ _ => rfl)

theorem invariant_action_commutator_mono (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second)
    (contained : first ≤ second) :
    invariantActionCommutator first first_invariant ≤ invariantActionCommutator second second_invariant := by
  let _action := invariantSubgroupAction first first_invariant
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, element, rfl⟩
  exact invariant_action_commutator_generator second second_invariant actorElement element.val
    (contained element.property)

theorem invariant_action_commutator_map_le (homomorphism : GroupType →* ImageType)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (parent : Subgroup GroupType) (imageParent : Subgroup ImageType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (image_invariant : ∀ actorElement : ActorType, ∀ element ∈ imageParent,
      actorElement • element ∈ imageParent)
    (image_le : parent.map homomorphism ≤ imageParent) :
    (invariantActionCommutator parent invariant).map homomorphism ≤
      invariantActionCommutator imageParent image_invariant := by
  let _action := invariantSubgroupAction parent invariant
  change ((actionCommutator (ActorType := ActorType) (GroupType := parent)).map parent.subtype).map
    homomorphism ≤ _
  rw [Subgroup.map_map]
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, element, rfl⟩
  change homomorphism (element.val⁻¹ * (actorElement • element.val)) ∈
    invariantActionCommutator imageParent image_invariant
  rw [map_mul, map_inv, equivariant]
  exact invariant_action_commutator_generator imageParent image_invariant actorElement
    (homomorphism element.val) (image_le (Subgroup.mem_map_of_mem homomorphism element.property))

theorem invariant_action_commutator_map_eq (homomorphism : GroupType →* ImageType)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (parent : Subgroup GroupType) (imageParent : Subgroup ImageType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (image_invariant : ∀ actorElement : ActorType, ∀ element ∈ imageParent,
      actorElement • element ∈ imageParent)
    (image_equal : parent.map homomorphism = imageParent) :
    (invariantActionCommutator parent invariant).map homomorphism =
      invariantActionCommutator imageParent image_invariant := by
  apply le_antisymm (invariant_action_commutator_map_le homomorphism equivariant parent imageParent
    invariant image_invariant image_equal.le)
  let _action := invariantSubgroupAction imageParent image_invariant
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, element, rfl⟩
  have member : element.val ∈ parent.map homomorphism := by
    rw [image_equal]
    exact element.property
  obtain ⟨representative, representative_member, mapped⟩ := member
  have generated := Subgroup.mem_map_of_mem homomorphism
    (invariant_action_commutator_generator parent invariant actorElement representative representative_member)
  rw [map_mul, map_inv, equivariant, mapped] at generated
  exact generated

theorem invariant_action_commutator_invariant_of_commuting
    {SecondActorType : Type secondActorUniverse} [Group SecondActorType]
    [MulDistribMulAction SecondActorType GroupType]
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element))
    (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (second_invariant : ∀ actorElement : SecondActorType, ∀ element ∈ parent,
      actorElement • element ∈ parent) :
    ∀ secondActor : SecondActorType, ∀ element ∈ invariantActionCommutator parent invariant,
      secondActor • element ∈ invariantActionCommutator parent invariant := by
  intro secondActor element member
  have image_le := invariant_action_commutator_map_le
    (MulDistribMulAction.toMonoidHom GroupType secondActor)
    (fun firstActor original => (commuting firstActor secondActor original).symm)
    parent parent invariant invariant (by
      rintro _ ⟨original, original_member, rfl⟩
      exact second_invariant secondActor original original_member)
  exact image_le (Subgroup.mem_map_of_mem _ member)

theorem invariant_action_commutator_trivial_iff (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    invariantActionCommutator parent invariant = ⊥ ↔
      ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element = element := by
  constructor
  · intro trivial actorElement element member
    have generated := invariant_action_commutator_generator parent invariant actorElement element member
    rw [trivial] at generated
    exact ((inv_mul_eq_one).mp (show element⁻¹ * (actorElement • element) = 1 from generated)).symm
  · intro fixed
    let _action := invariantSubgroupAction parent invariant
    have trivial : actionCommutator (ActorType := ActorType) (GroupType := parent) = ⊥ :=
      action_commutator_trivial_iff.mpr (fun actorElement element =>
        Subtype.ext (fixed actorElement element.val element.property))
    change (actionCommutator (ActorType := ActorType) (GroupType := parent)).map parent.subtype = ⊥
    rw [trivial, Subgroup.map_bot]

end CFSG.SignalizerFunctor.Helpers
