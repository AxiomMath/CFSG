module

public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutatorTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantMinimalNormal

public section

universe actorUniverse groupUniverse secondActorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {SecondActorType : Type secondActorUniverse} [Group SecondActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType] [MulDistribMulAction SecondActorType GroupType]

theorem abelian_subgroup_conjugation_eq (parent : Subgroup GroupType) [IsMulCommutative parent]
    (conjugator element : GroupType) (conjugator_member : conjugator ∈ parent) (member : element ∈ parent) :
    conjugator * element * conjugator⁻¹ = element := by
  have commute : conjugator * element = element * conjugator :=
    congrArg (fun internal : parent => internal.val)
      (mul_comm' (⟨conjugator, conjugator_member⟩ : parent) (⟨element, member⟩ : parent))
  rw [commute, mul_assoc, mul_inv_cancel, mul_one]

theorem action_commutator_le_of_fixed_normal_extension [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime SecondActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (parent : Subgroup GroupType) [parent.Normal]
    (fixed : ∀ actorElement : SecondActorType, ∀ element ∈ parent, actorElement • element = element)
    (target : Subgroup GroupType)
    (invariant : ∀ actorElement : SecondActorType, ∀ element ∈ target, actorElement • element ∈ target)
    (contained : actionCommutator (ActorType := SecondActorType) (GroupType := GroupType) ≤ target ⊔ parent) :
    actionCommutator (ActorType := SecondActorType) (GroupType := GroupType) ≤ target := by
  let commutators := actionCommutator (ActorType := SecondActorType) (GroupType := GroupType)
  have centralizes : commutators ≤ Subgroup.centralizer (parent : Set GroupType) :=
    action_commutator_centralizes_fixed_normal parent fixed
  rw [← coprime_action_commutator_idempotent prime prime_prime actor_pgroup coprime]
  apply Subgroup.map_le_iff_le_comap.mpr
  let _action := invariantSubgroupAction commutators action_commutator_invariant
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨actorElement, element, rfl⟩
  obtain ⟨targetElement, target_member, parentElement, parent_member, product⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (contained element.property)
  have difference : targetElement⁻¹ * (actorElement • targetElement) ∈ target :=
    target.mul_mem (target.inv_mem target_member) (invariant actorElement targetElement target_member)
  have fixed_parent : actorElement • parentElement = parentElement := fixed actorElement parentElement parent_member
  have commute_difference : parentElement * (targetElement⁻¹ * (actorElement • targetElement)) =
      (targetElement⁻¹ * (actorElement • targetElement)) * parentElement := by
    apply Subgroup.mem_centralizer_iff.mp
      (centralizes (action_commutator_generator actorElement targetElement)) parentElement parent_member
  change element.val⁻¹ * (actorElement • element.val) ∈ target
  rw [← product, mul_inv_rev, MulDistribMulAction.smul_mul, fixed_parent]
  have equal : parentElement⁻¹ * targetElement⁻¹ * ((actorElement • targetElement) * parentElement) =
      targetElement⁻¹ * (actorElement • targetElement) := by
    calc
      _ = parentElement⁻¹ * ((targetElement⁻¹ * (actorElement • targetElement)) * parentElement) := by group
      _ = parentElement⁻¹ * (parentElement * (targetElement⁻¹ * (actorElement • targetElement))) := by
        rw [commute_difference]
      _ = _ := by group
  rwa [equal]

theorem action_commutator_le_of_minimal_abelian_extension [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime SecondActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element))
    (parent : Subgroup GroupType) [parent.Normal] [IsMulCommutative parent]
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (second_invariant : ∀ actorElement : SecondActorType, ∀ element ∈ parent,
      actorElement • element ∈ parent)
    (minimal : ∀ smaller : Subgroup GroupType, smaller ≤ parent → smaller.Normal → smaller ≠ ⊥ →
      (∀ actorElement : ActorType, ∀ element ∈ smaller, actorElement • element ∈ smaller) →
      (∀ actorElement : SecondActorType, ∀ element ∈ smaller, actorElement • element ∈ smaller) →
      smaller = parent)
    (target : Subgroup GroupType)
    (target_invariant : ∀ actorElement : SecondActorType, ∀ element ∈ target,
      actorElement • element ∈ target)
    (contained : actionCommutator (ActorType := SecondActorType) (GroupType := GroupType) ≤ target ⊔ parent)
    (kernel_commutators_le : invariantActionCommutator parent second_invariant ≤ target) :
    actionCommutator (ActorType := SecondActorType) (GroupType := GroupType) ≤ target := by
  classical
  let kernelCommutators := invariantActionCommutator parent second_invariant
  by_cases trivial : kernelCommutators = ⊥
  · exact action_commutator_le_of_fixed_normal_extension prime prime_prime actor_pgroup coprime
      parent ((invariant_action_commutator_trivial_iff parent second_invariant).mp trivial)
      target target_invariant contained
  · let closure := Subgroup.normalClosure (kernelCommutators : Set GroupType)
    have closure_le : closure ≤ parent := Subgroup.normalClosure_le_normal
      (invariant_action_commutator_le parent second_invariant)
    have closure_nontrivial : closure ≠ ⊥ := by
      intro closure_trivial
      apply trivial
      apply le_bot_iff.mp
      exact (show kernelCommutators ≤ closure from Subgroup.subset_normalClosure).trans closure_trivial.le
    have closure_equal : closure = parent := minimal closure closure_le inferInstance closure_nontrivial
      (invariant_normal_closure kernelCommutators
        (invariant_action_commutator_invariant_of_commuting
          (fun secondActor firstActor element => (commuting firstActor secondActor element).symm)
          parent second_invariant first_invariant))
      (invariant_normal_closure kernelCommutators (invariant_action_commutator_invariant parent second_invariant))
    let commutators := actionCommutator (ActorType := SecondActorType) (GroupType := GroupType)
    let _commutatorsNormal : commutators.Normal := action_commutator_normal
    have factorization : commutators ⊔ FixedPoints.subgroup SecondActorType GroupType = ⊤ :=
      coprime_action_commutator_factorization prime prime_prime actor_pgroup coprime
    have fixed_normalizes : FixedPoints.subgroup SecondActorType GroupType ≤
        Subgroup.normalizer (kernelCommutators : Set GroupType) :=
      fixed_normalizes_invariant_action_commutator parent second_invariant Subgroup.le_normalizer_of_normal
    have conjugates_le : Group.conjugatesOfSet (kernelCommutators : Set GroupType) ⊆ (target : Set GroupType) := by
      intro element member
      obtain ⟨original, original_member, conjugate⟩ := Group.mem_conjugatesOfSet_iff.mp member
      obtain ⟨conjugator, rfl⟩ := isConj_iff.mp conjugate
      have conjugator_member : conjugator ∈ commutators ⊔ FixedPoints.subgroup SecondActorType GroupType := by
        rw [factorization]
        trivial
      obtain ⟨commutatorElement, commutator_member, fixedElement, fixed_member, product⟩ :=
        Subgroup.mem_sup_of_normal_left.mp conjugator_member
      obtain ⟨targetElement, target_member, parentElement, parent_member, inner_product⟩ :=
        Subgroup.mem_sup_of_normal_right.mp (contained commutator_member)
      have fixed_conjugate_member := Subgroup.le_normalizer_iff.mp fixed_normalizes fixedElement fixed_member
        original original_member
      have fixed_conjugate_parent := invariant_action_commutator_le parent second_invariant fixed_conjugate_member
      have parent_conjugate : parentElement * (fixedElement * original * fixedElement⁻¹) * parentElement⁻¹ =
          fixedElement * original * fixedElement⁻¹ :=
        abelian_subgroup_conjugation_eq parent parentElement _ parent_member fixed_conjugate_parent
      have equal : conjugator * original * conjugator⁻¹ =
          targetElement * (fixedElement * original * fixedElement⁻¹) * targetElement⁻¹ := by
        rw [← product, ← inner_product]
        calc
          _ = targetElement * (parentElement * (fixedElement * original * fixedElement⁻¹) * parentElement⁻¹) *
              targetElement⁻¹ := by group
          _ = _ := by rw [parent_conjugate]
      rw [equal]
      exact target.mul_mem (target.mul_mem target_member (kernel_commutators_le fixed_conjugate_member))
        (target.inv_mem target_member)
    have parent_le : parent ≤ target := by
      rw [← closure_equal]
      exact (Subgroup.closure_le target).mpr conjugates_le
    exact contained.trans (sup_le le_rfl parent_le)

end CFSG.SignalizerFunctor.Helpers
