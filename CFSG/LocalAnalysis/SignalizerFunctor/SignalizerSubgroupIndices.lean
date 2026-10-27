module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerRestriction
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageIndices

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

theorem centralizer_image_of_injective (homomorphism : GroupType →* ImageType)
    (injective : Function.Injective homomorphism) (actor target : Subgroup GroupType) :
    (target ⊓ Subgroup.centralizer (actor : Set GroupType)).map homomorphism =
      target.map homomorphism ⊓
        Subgroup.centralizer (actor.map homomorphism : Set ImageType) := by
  apply le_antisymm
  · rintro imageElement ⟨element, member, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem homomorphism member.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro imageActor ⟨actorElement, actor_member, rfl⟩
    simpa only [map_mul] using congrArg homomorphism
      (Subgroup.mem_centralizer_iff.mp member.2 actorElement actor_member)
  · rintro imageElement ⟨⟨element, member, rfl⟩, fixed⟩
    refine ⟨element, ⟨member, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro actorElement actor_member
    apply injective
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp fixed
      (homomorphism actorElement) (Subgroup.mem_map_of_mem homomorphism actor_member)

theorem normalizer_comap_le (homomorphism : GroupType →* ImageType)
    (actor : Subgroup GroupType) (target : Subgroup ImageType)
    (normalized : actor.map homomorphism ≤ Subgroup.normalizer (target : Set ImageType)) :
    actor ≤ Subgroup.normalizer (target.comap homomorphism : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actorElement actor_member element member
  change homomorphism (actorElement * element * actorElement⁻¹) ∈ target
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.le_normalizer_iff.mp normalized (homomorphism actorElement)
    (Subgroup.mem_map_of_mem homomorphism actor_member) (homomorphism element) member

theorem subgroup_actor_map (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient) :
    (actor.subgroupOf ambient).map ambient.subtype = actor := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr contained]

theorem elementary_abelian_subgroupOf (prime : ℕ) (actor ambient : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor) : IsElemAbelian prime (actor.subgroupOf ambient) := by
  let := elementary.1
  refine ⟨inferInstance, ?_⟩
  intro element member
  apply Subtype.ext
  exact elementary.2 element.val member

theorem signalizer_subgroup_index_member (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (selected : Subgroup ambient)
    (member : selected ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient)) :
    selected.map ambient.subtype ∈ signalizerFunctorEk prime rank actor := by
  have actor_injective : Function.Injective (ambient.subtype.domRestrict (actor.subgroupOf ambient)) :=
    ambient.subtype_injective.comp (actor.subgroupOf ambient).subtype_injective
  have transported := signalizer_image_member prime rank ambient.subtype
    (actor.subgroupOf ambient) actor_injective selected member
  rwa [subgroup_actor_map actor ambient contained] at transported

theorem signalizer_ambient_index_member (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    selected.subgroupOf ambient ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient) := by
  refine ⟨Subgroup.comap_mono member.1, ?_⟩
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (member.1.trans contained)).toEquiv).trans
    member.2

@[expose] def signalizerSubgroupValues (ambient : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (selected : Subgroup ambient) :
    Subgroup ambient :=
  (values (selected.map ambient.subtype)).subgroupOf ambient

theorem signalizer_subgroup_value_map (ambient : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (selected : Subgroup ambient) :
    (signalizerSubgroupValues ambient values selected).map ambient.subtype =
      signalizerRestriction values ambient (selected.map ambient.subtype) :=
  Subgroup.subgroupOf_map_subtype _ _

theorem signalizer_subgroup_value_at_ambient_index (ambient selected : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (contained : selected ≤ ambient) :
    signalizerSubgroupValues ambient values (selected.subgroupOf ambient) =
      (values selected).subgroupOf ambient := by
  unfold signalizerSubgroupValues
  rw [subgroup_actor_map selected ambient contained]

end CFSG.SignalizerFunctor.Helpers
