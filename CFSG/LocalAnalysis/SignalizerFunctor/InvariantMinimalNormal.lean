module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions
public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalNormal

public section

universe actorUniverse groupUniverse secondActorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {SecondActorType : Type secondActorUniverse} [Group SecondActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction SecondActorType GroupType]

theorem invariant_characteristic_subgroup (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (internal : Subgroup parent) [internal.Characteristic] :
    ∀ actorElement : ActorType, ∀ element ∈ internal.map parent.subtype,
      actorElement • element ∈ internal.map parent.subtype := by
  let _action := invariantSubgroupAction parent invariant
  rintro actorElement _ ⟨representative, member, rfl⟩
  have preserved : actorElement • representative ∈ internal :=
    Subgroup.characteristic_iff_le_comap.mp inferInstance
      (MulDistribMulAction.toMulEquiv parent actorElement) member
  exact Subgroup.mem_map_of_mem parent.subtype preserved

theorem invariant_normal_closure (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) :
    ∀ actorElement : ActorType, ∀ element ∈ Subgroup.normalClosure (subgroup : Set GroupType),
      actorElement • element ∈ Subgroup.normalClosure (subgroup : Set GroupType) := by
  intro actorElement element member
  let homomorphism := MulDistribMulAction.toMonoidHom GroupType actorElement
  have image_le : (Subgroup.normalClosure (subgroup : Set GroupType)).map homomorphism ≤
      Subgroup.normalClosure (subgroup : Set GroupType) := by
    apply (Subgroup.map_normalClosure_le _ homomorphism).trans
    apply Subgroup.normalClosure_mono
    rintro _ ⟨original, original_member, rfl⟩
    exact invariant actorElement original original_member
  exact image_le (Subgroup.mem_map_of_mem homomorphism member)

theorem solvable_minimal_invariant_normal_exists [Finite GroupType] [Nontrivial GroupType]
    [Group.IsSolvable GroupType] :
    ∃ parent : Subgroup GroupType, parent.Normal ∧ parent ≠ ⊥ ∧ IsMulCommutative parent ∧
      (∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) ∧
      (∀ actorElement : SecondActorType, ∀ element ∈ parent, actorElement • element ∈ parent) ∧
      (∀ smaller : Subgroup GroupType, smaller ≤ parent → smaller.Normal → smaller ≠ ⊥ →
        (∀ actorElement : ActorType, ∀ element ∈ smaller, actorElement • element ∈ smaller) →
        (∀ actorElement : SecondActorType, ∀ element ∈ smaller, actorElement • element ∈ smaller) →
        smaller = parent) := by
  classical
  let property : Subgroup GroupType → Prop := fun subgroup => subgroup.Normal ∧ subgroup ≠ ⊥ ∧
    (∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) ∧
    (∀ actorElement : SecondActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup)
  have whole_property : property ⊤ := ⟨inferInstance, top_ne_bot, fun _ _ _ => trivial,
    fun _ _ _ => trivial⟩
  obtain ⟨parent, _, minimal⟩ := Finite.exists_le_minimal whole_property
  let _normal := minimal.prop.1
  have minimal_normal : ∀ smaller : Subgroup GroupType, smaller ≤ parent → smaller.Normal → smaller ≠ ⊥ →
      (∀ actorElement : ActorType, ∀ element ∈ smaller, actorElement • element ∈ smaller) →
      (∀ actorElement : SecondActorType, ∀ element ∈ smaller, actorElement • element ∈ smaller) →
      smaller = parent := by
    intro smaller contained normal nontrivial first_invariant second_invariant
    exact minimal.eq_of_le ⟨normal, nontrivial, first_invariant, second_invariant⟩ contained
  have derived_trivial : (commutator parent).map parent.subtype = ⊥ := by
    by_contra nontrivial
    have equality := minimal_normal _ (Subgroup.map_subtype_le _) (normal_of_characteristic_subgroup parent _)
      nontrivial (invariant_characteristic_subgroup parent minimal.prop.2.2.1 _)
      (invariant_characteristic_subgroup parent minimal.prop.2.2.2 _)
    have cardinality := congrArg (fun subgroup : Subgroup GroupType => Nat.card subgroup) equality
    rw [Subgroup.card_map_of_injective parent.subtype_injective] at cardinality
    let : Nontrivial parent := (Subgroup.nontrivial_iff_ne_bot parent).mpr minimal.prop.2.1
    have smaller : Nat.card (commutator parent) < Nat.card parent := by
      apply lt_of_le_of_ne (commutator parent).card_le_card_group
      intro same_card
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial parent).ne
        ((commutator parent).card_eq_iff_eq_top.mp same_card)
    exact smaller.ne cardinality
  have commutative : IsMulCommutative parent := (commutator_eq_bot_iff parent).mp
    ((Subgroup.map_eq_bot_iff_of_injective _ parent.subtype_injective).mp derived_trivial)
  exact ⟨parent, minimal.prop.1, minimal.prop.2.1, commutative, minimal.prop.2.2.1,
    minimal.prop.2.2.2, minimal_normal⟩

end CFSG.SignalizerFunctor.Helpers
