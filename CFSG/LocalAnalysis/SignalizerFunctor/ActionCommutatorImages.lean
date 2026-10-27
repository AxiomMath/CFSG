module

public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutators
public import Mathlib.Order.CompletePartialOrder

public section

universe actorUniverse groupUniverse imageUniverse secondActorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction ActorType ImageType]

theorem action_commutator_map_le (homomorphism : GroupType →* ImageType)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element) :
    (actionCommutator (ActorType := ActorType) (GroupType := GroupType)).map homomorphism ≤
      actionCommutator (ActorType := ActorType) (GroupType := ImageType) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, element, rfl⟩
  change homomorphism (element⁻¹ * (actorElement • element)) ∈ actionCommutator (ActorType := ActorType)
  rw [map_mul, map_inv, equivariant]
  exact action_commutator_generator actorElement _

theorem action_commutator_map_surjective (homomorphism : GroupType →* ImageType)
    (surjective : Function.Surjective homomorphism)
    (equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element) :
    (actionCommutator (ActorType := ActorType) (GroupType := GroupType)).map homomorphism =
      actionCommutator (ActorType := ActorType) (GroupType := ImageType) := by
  apply le_antisymm (action_commutator_map_le homomorphism equivariant)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, imageElement, rfl⟩
  obtain ⟨element, rfl⟩ := surjective imageElement
  have mapped := Subgroup.mem_map_of_mem homomorphism (action_commutator_generator actorElement element)
  rwa [map_mul, map_inv, equivariant] at mapped

theorem action_commutator_trivial_iff :
    actionCommutator (ActorType := ActorType) (GroupType := GroupType) = ⊥ ↔
      ∀ actorElement : ActorType, ∀ element : GroupType, actorElement • element = element := by
  constructor
  · intro trivial actorElement element
    have generator := action_commutator_generator actorElement element
    rw [trivial] at generator
    have equal : element⁻¹ * (actorElement • element) = 1 := generator
    exact ((inv_mul_eq_one).mp equal).symm
  · intro fixed
    apply le_bot_iff.mp
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, element, rfl⟩
    rw [fixed, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem action_commutator_invariant_of_commuting
    {SecondActorType : Type secondActorUniverse} [Group SecondActorType]
    [MulDistribMulAction SecondActorType GroupType]
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    ∀ secondActor : SecondActorType, ∀ element ∈ actionCommutator (ActorType := ActorType) (GroupType := GroupType),
      secondActor • element ∈ actionCommutator (ActorType := ActorType) := by
  intro secondActor element member
  have image_le := action_commutator_map_le (MulDistribMulAction.toMonoidHom GroupType secondActor)
    (fun firstActor original => (commuting firstActor secondActor original).symm)
  exact image_le (Subgroup.mem_map_of_mem _ member)

theorem action_commutator_centralizes_fixed_normal (normal : Subgroup GroupType) [normal.Normal]
    (fixed : ∀ actorElement : ActorType, ∀ element ∈ normal, actorElement • element = element) :
    actionCommutator (ActorType := ActorType) (GroupType := GroupType) ≤ Subgroup.centralizer (normal : Set GroupType) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, element, rfl⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro normalElement member
  have conjugated_member := Subgroup.Normal.conj_mem (inferInstance : normal.Normal)
    normalElement member element
  have preserved := fixed actorElement _ conjugated_member
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, fixed actorElement normalElement member,
    smul_inv'] at preserved
  have conjugate_equal : (actorElement • element) * normalElement * (actorElement • element)⁻¹ =
      element * normalElement * element⁻¹ := preserved
  calc
    normalElement * (element⁻¹ * (actorElement • element)) =
        element⁻¹ * (element * normalElement * element⁻¹) * (actorElement • element) := by group
    _ = element⁻¹ * ((actorElement • element) * normalElement * (actorElement • element)⁻¹) *
        (actorElement • element) := by rw [conjugate_equal]
    _ = (element⁻¹ * (actorElement • element)) * normalElement := by group

end CFSG.SignalizerFunctor.Helpers
