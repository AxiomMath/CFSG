module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimePowerFixedFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutatorTransport

public section

universe actorUniverse groupUniverse secondActorUniverse imageUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [CommGroup ActorType]
variable {SecondActorType : Type secondActorUniverse} [Group SecondActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction SecondActorType GroupType]

theorem commuting_fixed_subgroup_invariant
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element))
    (actorSubgroup : Subgroup ActorType) :
    ∀ secondActor : SecondActorType, ∀ element ∈ FixedPoints.subgroup actorSubgroup GroupType,
      secondActor • element ∈ FixedPoints.subgroup actorSubgroup GroupType := by
  intro secondActor element fixed firstActor
  change firstActor.val • (secondActor • element) = secondActor • element
  rw [commuting]
  exact congrArg (fun original : GroupType => secondActor • original) (fixed firstActor)

@[expose] def fixedActionCommutatorHull
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) : Subgroup GroupType :=
  ⨆ actorSubgroup : Subgroup ActorType, ⨆ (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
    invariantActionCommutator (FixedPoints.subgroup actorSubgroup GroupType)
      (commuting_fixed_subgroup_invariant commuting actorSubgroup)

theorem fixed_action_commutator_hull_le
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    fixedActionCommutatorHull commuting ≤ actionCommutator (ActorType := SecondActorType) := by
  exact iSup_le fun _ => iSup_le fun _ => invariant_action_commutator_le_global _ _

theorem fixed_action_commutator_hull_second_invariant
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    ∀ secondActor : SecondActorType, ∀ element ∈ fixedActionCommutatorHull commuting,
      secondActor • element ∈ fixedActionCommutatorHull commuting := by
  intro secondActor element member
  have image_le : (fixedActionCommutatorHull commuting).map
      (MulDistribMulAction.toMonoidHom GroupType secondActor) ≤ fixedActionCommutatorHull commuting := by
    unfold fixedActionCommutatorHull
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro actorSubgroup
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro cyclic
    apply le_trans _ (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
    rintro _ ⟨original, original_member, rfl⟩
    exact invariant_action_commutator_invariant _ _ secondActor original original_member
  exact image_le (Subgroup.mem_map_of_mem _ member)

theorem fixed_action_commutator_hull_first_invariant
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    ∀ firstActor : ActorType, ∀ element ∈ fixedActionCommutatorHull commuting,
      firstActor • element ∈ fixedActionCommutatorHull commuting := by
  intro firstActor element member
  have image_le : (fixedActionCommutatorHull commuting).map
      (MulDistribMulAction.toMonoidHom GroupType firstActor) ≤ fixedActionCommutatorHull commuting := by
    unfold fixedActionCommutatorHull
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro actorSubgroup
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro cyclic
    apply le_trans _ (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
    rintro _ ⟨original, original_member, rfl⟩
    exact invariant_action_commutator_invariant_of_commuting
      (fun secondActor actorElement original => (commuting actorElement secondActor original).symm)
      _ _ (fixed_subgroup_invariant_of_commutative_actor actorSubgroup)
      firstActor original original_member
  exact image_le (Subgroup.mem_map_of_mem _ member)

theorem commuting_subgroup_actions (parent : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (second_invariant : ∀ actorElement : SecondActorType, ∀ element ∈ parent,
      actorElement • element ∈ parent)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    let _firstAction := invariantSubgroupAction parent first_invariant
    let _secondAction := invariantSubgroupAction parent second_invariant
    ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : parent,
      firstActor • (secondActor • element) = secondActor • (firstActor • element) := by
  let _firstAction := invariantSubgroupAction parent first_invariant
  let _secondAction := invariantSubgroupAction parent second_invariant
  exact fun firstActor secondActor element => Subtype.ext (commuting firstActor secondActor element.val)

theorem commuting_quotient_actions (parent : Subgroup GroupType) [parent.Normal]
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (second_invariant : ∀ actorElement : SecondActorType, ∀ element ∈ parent,
      actorElement • element ∈ parent)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    let _firstAction := invariantQuotientAction parent first_invariant
    let _secondAction := invariantQuotientAction parent second_invariant
    ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType ⧸ parent,
      firstActor • (secondActor • element) = secondActor • (firstActor • element) := by
  let _firstAction := invariantQuotientAction parent first_invariant
  let _secondAction := invariantQuotientAction parent second_invariant
  change ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType ⧸ parent,
    firstActor • (secondActor • element) = secondActor • (firstActor • element)
  intro firstActor secondActor element
  induction element using QuotientGroup.induction_on with
  | H original =>
    exact congrArg (QuotientGroup.mk' parent) (commuting firstActor secondActor original)

theorem fixed_action_commutator_hull_map_le
    {ImageType : Type imageUniverse} [Group ImageType]
    [MulDistribMulAction ActorType ImageType] [MulDistribMulAction SecondActorType ImageType]
    (homomorphism : GroupType →* ImageType)
    (first_equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (second_equivariant : ∀ actorElement : SecondActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element))
    (image_commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : ImageType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    (fixedActionCommutatorHull commuting).map homomorphism ≤ fixedActionCommutatorHull image_commuting := by
  unfold fixedActionCommutatorHull
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro actorSubgroup
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro cyclic
  apply le_trans _ (le_iSup_of_le actorSubgroup (le_iSup_of_le cyclic le_rfl))
  apply invariant_action_commutator_map_le homomorphism second_equivariant
  rintro _ ⟨representative, fixed, rfl⟩ actorElement
  change actorElement.val • homomorphism representative = homomorphism representative
  rw [← first_equivariant, show actorElement.val • representative = representative from fixed actorElement]

theorem fixed_action_commutator_hull_map_eq
    {ImageType : Type imageUniverse} [Group ImageType]
    [MulDistribMulAction ActorType ImageType] [MulDistribMulAction SecondActorType ImageType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (homomorphism : GroupType →* ImageType) (surjective : Function.Surjective homomorphism)
    (kernel_coprime : Nat.Coprime prime (Nat.card homomorphism.ker))
    (first_equivariant : ∀ actorElement : ActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (second_equivariant : ∀ actorElement : SecondActorType, ∀ element : GroupType,
      homomorphism (actorElement • element) = actorElement • homomorphism element)
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element))
    (image_commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : ImageType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    (fixedActionCommutatorHull commuting).map homomorphism = fixedActionCommutatorHull image_commuting := by
  unfold fixedActionCommutatorHull
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro actorSubgroup
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro cyclic
  apply invariant_action_commutator_map_eq homomorphism second_equivariant
  exact fixed_subgroup_map prime prime_prime (actor_pgroup.to_subgroup actorSubgroup) homomorphism
    surjective (fun actorElement element => first_equivariant actorElement.val element) kernel_coprime

theorem abelian_action_commutator_generation
    {AbelianType : Type groupUniverse} [CommGroup AbelianType]
    [MulDistribMulAction SecondActorType AbelianType]
    {IndexType : Sort indexUniverse} (family : IndexType → Subgroup AbelianType)
    (invariant : ∀ index : IndexType, ∀ actorElement : SecondActorType, ∀ element ∈ family index,
      actorElement • element ∈ family index) (generated : iSup family = ⊤) :
    actionCommutator (ActorType := SecondActorType) (GroupType := AbelianType) =
      ⨆ index : IndexType, invariantActionCommutator (family index) (invariant index) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, element, rfl⟩
    have member : element ∈ iSup family := by rw [generated]; trivial
    refine Subgroup.iSup_induction family
      (C := fun original => original⁻¹ * (actorElement • original) ∈
        ⨆ index : IndexType, invariantActionCommutator (family index) (invariant index))
      member (fun index original original_member => ?_) ?_
      (fun first second first_difference second_difference => ?_)
    · have contained : invariantActionCommutator (family index) (invariant index) ≤
          ⨆ otherIndex : IndexType, invariantActionCommutator (family otherIndex) (invariant otherIndex) :=
        le_iSup_of_le index le_rfl
      exact contained
        (invariant_action_commutator_generator (family index) (invariant index) actorElement original original_member)
    · simp only [inv_one, smul_one, mul_one]
      exact Subgroup.one_mem _
    · have equal : (first * second)⁻¹ * (actorElement • (first * second)) =
          (first⁻¹ * (actorElement • first)) * (second⁻¹ * (actorElement • second)) := by
        rw [mul_inv_rev, MulDistribMulAction.smul_mul]
        ac_rfl
      rw [equal]
      exact Subgroup.mul_mem _ first_difference second_difference
  · exact iSup_le fun index => invariant_action_commutator_le_global (family index) (invariant index)

theorem abelian_fixed_action_commutator_hull
    {AbelianType : Type groupUniverse} [CommGroup AbelianType] [Finite AbelianType]
    [Finite ActorType] [MulDistribMulAction ActorType AbelianType]
    [MulDistribMulAction SecondActorType AbelianType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card AbelianType))
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : AbelianType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    fixedActionCommutatorHull commuting = actionCommutator (ActorType := SecondActorType) := by
  unfold fixedActionCommutatorHull
  rw [iSup_subtype']
  exact (abelian_action_commutator_generation
    (fun index : {actorSubgroup : Subgroup ActorType // IsCyclic (ActorType ⧸ actorSubgroup)} =>
      FixedPoints.subgroup index.val AbelianType)
    (fun index => commuting_fixed_subgroup_invariant commuting index.val)
    (by
      simpa only [iSup_subtype'] using coprime_cyclic_quotient_generation prime prime_prime
        ActorType actor_pgroup AbelianType coprime)).symm

end CFSG.SignalizerFunctor.Helpers
