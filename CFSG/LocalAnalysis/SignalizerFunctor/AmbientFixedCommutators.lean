module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.OrderFixedCommutators

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped commutatorElement

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem commuting_conjugation_actions (firstActor secondActor target : Subgroup GroupType)
    (first_normalized : firstActor ≤ Subgroup.normalizer (target : Set GroupType))
    (second_normalized : secondActor ≤ Subgroup.normalizer (target : Set GroupType))
    (centralizes : firstActor ≤ Subgroup.centralizer (secondActor : Set GroupType)) :
    let _firstAction := conjugationAction firstActor target first_normalized
    let _secondAction := conjugationAction secondActor target second_normalized
    ∀ firstElement : firstActor, ∀ secondElement : secondActor, ∀ element : target,
      firstElement • (secondElement • element) = secondElement • (firstElement • element) := by
  let _firstAction := conjugationAction firstActor target first_normalized
  let _secondAction := conjugationAction secondActor target second_normalized
  change ∀ firstElement : firstActor, ∀ secondElement : secondActor, ∀ element : target,
    firstElement • (secondElement • element) = secondElement • (firstElement • element)
  intro firstElement secondElement element
  apply Subtype.ext
  have commute := Subgroup.mem_centralizer_iff.mp (centralizes firstElement.property)
    secondElement.val secondElement.property
  change firstElement.val * (secondElement.val * element.val * secondElement.val⁻¹) * firstElement.val⁻¹ =
    secondElement.val * (firstElement.val * element.val * firstElement.val⁻¹) * secondElement.val⁻¹
  calc
    _ = (firstElement.val * secondElement.val) * element.val * (firstElement.val * secondElement.val)⁻¹ := by group
    _ = (secondElement.val * firstElement.val) * element.val * (secondElement.val * firstElement.val)⁻¹ := by
      rw [commute]
    _ = _ := by group

theorem conjugation_internal_fixed_subgroup_map (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) (actorSubgroup : Subgroup actor) :
    let _action := conjugationAction actor target normalized
    (FixedPoints.subgroup actorSubgroup target).map target.subtype =
      target ⊓ Subgroup.centralizer ((actorSubgroup.map actor.subtype : Subgroup GroupType) : Set GroupType) := by
  let _action := conjugationAction actor target normalized
  ext element
  constructor
  · rintro ⟨internal, fixed, rfl⟩
    refine ⟨internal.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨actorElement, actor_member, rfl⟩
    have equal := congrArg (fun original : target => original.val)
      (fixed (⟨actorElement, actor_member⟩ : actorSubgroup))
    exact mul_inv_eq_iff_eq_mul.mp equal
  · rintro ⟨member, central⟩
    refine ⟨⟨element, member⟩, ?_, rfl⟩
    intro actorElement
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp central actorElement.val.val
      (Subgroup.mem_map_of_mem actor.subtype actorElement.property))

theorem conjugation_invariant_action_commutator_map (actor parent : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType)) (internal : Subgroup parent)
    (invariant :
      let _action := conjugationAction actor parent normalized
      ∀ actorElement : actor, ∀ element ∈ internal, actorElement • element ∈ internal) :
    let _action := conjugationAction actor parent normalized
    (invariantActionCommutator internal invariant).map parent.subtype =
      ⁅internal.map parent.subtype, actor⁆ := by
  let _action := conjugationAction actor parent normalized
  let _internalAction := invariantSubgroupAction internal invariant
  apply le_antisymm
  · change ((actionCommutator (ActorType := actor) (GroupType := internal)).map internal.subtype).map
      parent.subtype ≤ _
    rw [Subgroup.map_map]
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, element, rfl⟩
    have generated := Subgroup.commutator_mem_commutator
      (Subgroup.inv_mem _ (Subgroup.mem_map_of_mem parent.subtype element.property)) actorElement.property
    change ⁅element.val.val⁻¹, actorElement.val⁆ ∈
      ⁅internal.map parent.subtype, actor⁆ at generated
    change element.val.val⁻¹ * (actorElement.val * element.val.val * actorElement.val⁻¹) ∈
      ⁅internal.map parent.subtype, actor⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using generated
  · apply Subgroup.commutator_le.mpr
    rintro _ ⟨element, member, rfl⟩ actorElement actor_member
    have generated := Subgroup.mem_map_of_mem parent.subtype
      (invariant_action_commutator_generator internal invariant (⟨actorElement, actor_member⟩ : actor)
        element⁻¹ (internal.inv_mem member))
    change element.val⁻¹⁻¹ * (actorElement * element.val⁻¹ * actorElement⁻¹) ∈
      (invariantActionCommutator internal invariant).map parent.subtype at generated
    change ⁅element.val, actorElement⁆ ∈
      (invariantActionCommutator internal invariant).map parent.subtype
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using generated

theorem solvable_normalized_order_fixed_commutator_generation [Finite GroupType]
    (prime rank actionPrime : ℕ) (prime_prime : prime.Prime) (action_prime : actionPrime.Prime)
    (actor secondActor target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor) (second_pgroup : IsPGroup actionPrime secondActor)
    (solvable : Group.IsSolvable target)
    (first_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (second_normalized : secondActor ≤ Subgroup.normalizer (target : Set GroupType))
    (centralizes : actor ≤ Subgroup.centralizer (secondActor : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target))
    (second_coprime : Nat.Coprime actionPrime (Nat.card target)) :
    ⁅target, secondActor⁆ = ⨆ selected ∈ signalizerFunctorEk prime rank actor,
      ⁅target ⊓ Subgroup.centralizer (selected : Set GroupType), secondActor⁆ := by
  let := elementary.1
  let _actorCommGroup : CommGroup actor := { actor.toGroup with mul_comm := mul_comm' }
  let := solvable
  let _firstAction := conjugationAction actor target first_normalized
  let _secondAction := conjugationAction secondActor target second_normalized
  have commuting := commuting_conjugation_actions actor secondActor target first_normalized second_normalized centralizes
  have generated := solvable_order_fixed_action_commutator_hull prime rank actionPrime prime_prime action_prime
    (fun element : actor => Subtype.ext (elementary.2 element.val element.property)) large second_pgroup
    coprime second_coprime commuting
  have mapped := congrArg (Subgroup.map target.subtype) generated
  rw [conjugation_action_commutator_map secondActor target second_normalized] at mapped
  apply le_antisymm
  · rw [← mapped]
    unfold orderFixedActionCommutatorHull
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro actorSubgroup
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro cardinality
    let embedded := actorSubgroup.map actor.subtype
    have embedded_member : embedded ∈ signalizerFunctorEk prime rank actor := by
      refine ⟨Subgroup.map_subtype_le _, ?_⟩
      rw [Subgroup.card_map_of_injective actor.subtype_injective]
      exact cardinality
    apply le_trans _ (le_iSup_of_le embedded (le_iSup_of_le embedded_member le_rfl))
    rw [conjugation_invariant_action_commutator_map secondActor target second_normalized,
      conjugation_internal_fixed_subgroup_map actor target first_normalized]
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact Subgroup.commutator_mono inf_le_left le_rfl

end CFSG.SignalizerFunctor.Helpers
