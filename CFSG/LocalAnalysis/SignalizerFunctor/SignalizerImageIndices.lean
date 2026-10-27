module

public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

@[expose] def subgroupImageHom (homomorphism : GroupType →* ImageType)
    (subgroup : Subgroup GroupType) : subgroup →* subgroup.map homomorphism :=
  (homomorphism.domRestrict subgroup).codRestrict (subgroup.map homomorphism)
    (fun element => Subgroup.mem_map_of_mem homomorphism element.property)

theorem subgroup_image_hom_surjective (homomorphism : GroupType →* ImageType)
    (subgroup : Subgroup GroupType) : Function.Surjective (subgroupImageHom homomorphism subgroup) := by
  intro imageElement
  obtain ⟨element, member, equality⟩ := imageElement.property
  exact ⟨⟨element, member⟩, Subtype.ext equality⟩

theorem subgroup_image_card_of_injective (homomorphism : GroupType →* ImageType)
    (subgroup : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict subgroup)) :
    Nat.card (subgroup.map homomorphism) = Nat.card subgroup := by
  have image_injective : Function.Injective (subgroupImageHom homomorphism subgroup) := by
    intro first second equal
    apply injective
    exact congrArg Subtype.val equal
  exact (Nat.card_congr (MulEquiv.ofBijective (subgroupImageHom homomorphism subgroup)
    ⟨image_injective, subgroup_image_hom_surjective homomorphism subgroup⟩).toEquiv).symm

@[expose] def signalizerImageIndex (homomorphism : GroupType →* ImageType)
    (actor : Subgroup GroupType) (selected : Subgroup ImageType) : Subgroup GroupType :=
  selected.comap homomorphism ⊓ actor

theorem signalizer_image_index_map (homomorphism : GroupType →* ImageType)
    (actor : Subgroup GroupType) (selected : Subgroup ImageType)
    (contained : selected ≤ actor.map homomorphism) :
    (signalizerImageIndex homomorphism actor selected).map homomorphism = selected := by
  apply le_antisymm
  · rintro imageElement ⟨element, member, rfl⟩
    exact member.1
  · intro imageElement member
    obtain ⟨element, actor_member, rfl⟩ := contained member
    exact ⟨element, ⟨member, actor_member⟩, rfl⟩

theorem signalizer_image_index_of_map (homomorphism : GroupType →* ImageType)
    (actor selected : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (contained : selected ≤ actor) :
    signalizerImageIndex homomorphism actor (selected.map homomorphism) = selected := by
  apply le_antisymm
  · rintro element ⟨⟨representative, member, equality⟩, actor_member⟩
    have equal : (⟨representative, contained member⟩ : actor) = ⟨element, actor_member⟩ :=
      injective equality
    have ambient_equal := congrArg (fun internal : actor => internal.val) equal
    change representative = element at ambient_equal
    exact ambient_equal ▸ member
  · intro element member
    exact ⟨Subgroup.mem_map_of_mem homomorphism member, contained member⟩

theorem signalizer_image_index_member (prime rank : ℕ)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (selected : Subgroup ImageType)
    (member : selected ∈ signalizerFunctorEk prime rank (actor.map homomorphism)) :
    signalizerImageIndex homomorphism actor selected ∈ signalizerFunctorEk prime rank actor := by
  refine ⟨inf_le_right, ?_⟩
  have restricted_injective : Function.Injective
      (homomorphism.domRestrict (signalizerImageIndex homomorphism actor selected)) := by
    intro first second equality
    have equal : (⟨first.val, first.property.2⟩ : actor) =
        ⟨second.val, second.property.2⟩ := injective equality
    exact Subtype.ext (congrArg (fun internal : actor => internal.val) equal)
  have card := subgroup_image_card_of_injective homomorphism
    (signalizerImageIndex homomorphism actor selected) restricted_injective
  rw [signalizer_image_index_map homomorphism actor selected member.1] at card
  exact card.symm.trans member.2

theorem signalizer_image_member (prime rank : ℕ)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    selected.map homomorphism ∈ signalizerFunctorEk prime rank (actor.map homomorphism) := by
  refine ⟨Subgroup.map_mono member.1, ?_⟩
  have restricted_injective : Function.Injective (homomorphism.domRestrict selected) := by
    intro first second equality
    have equal : (⟨first.val, member.1 first.property⟩ : actor) =
        ⟨second.val, member.1 second.property⟩ := injective equality
    exact Subtype.ext (congrArg (fun internal : actor => internal.val) equal)
  exact (subgroup_image_card_of_injective homomorphism selected restricted_injective).trans member.2

theorem elementary_abelian_image (prime : ℕ) (homomorphism : GroupType →* ImageType)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor) :
    IsElemAbelian prime (actor.map homomorphism) := CFSG.Open.IsElemAbelian.map elementary _

@[expose] def signalizerImageValues (homomorphism : GroupType →* ImageType)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (selected : Subgroup ImageType) : Subgroup ImageType :=
  (values (signalizerImageIndex homomorphism actor selected)).map homomorphism

theorem signalizer_image_value_of_map (homomorphism : GroupType →* ImageType)
    (actor selected : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (contained : selected ≤ actor) :
    signalizerImageValues homomorphism actor values (selected.map homomorphism) =
      (values selected).map homomorphism := by
  unfold signalizerImageValues
  rw [signalizer_image_index_of_map homomorphism actor selected injective contained]

end CFSG.SignalizerFunctor.Helpers
