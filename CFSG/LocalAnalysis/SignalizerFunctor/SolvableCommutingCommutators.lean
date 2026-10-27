module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedActionCommutatorHull
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutatorKernel

public section

universe actorUniverse groupUniverse secondActorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem solvable_fixed_action_commutator_hull
    (prime actionPrime : ℕ) (prime_prime : prime.Prime) (action_prime : actionPrime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (SecondActorType : Type secondActorUniverse) [Group SecondActorType]
    (actor_pgroup : IsPGroup prime ActorType) (second_pgroup : IsPGroup actionPrime SecondActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] [Group.IsSolvable GroupType]
    [MulDistribMulAction ActorType GroupType] [MulDistribMulAction SecondActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (second_coprime : Nat.Coprime actionPrime (Nat.card GroupType))
    (commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : GroupType,
      firstActor • (secondActor • element) = secondActor • (firstActor • element)) :
    fixedActionCommutatorHull commuting = actionCommutator (ActorType := SecondActorType) := by
  classical
  suffices general_result : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType] [Group.IsSolvable TargetType]
        [MulDistribMulAction ActorType TargetType] [MulDistribMulAction SecondActorType TargetType],
        Nat.card TargetType = order → Nat.Coprime prime (Nat.card TargetType) →
        Nat.Coprime actionPrime (Nat.card TargetType) →
        ∀ commuting : ∀ firstActor : ActorType, ∀ secondActor : SecondActorType, ∀ element : TargetType,
          firstActor • (secondActor • element) = secondActor • (firstActor • element),
        fixedActionCommutatorHull commuting = actionCommutator (ActorType := SecondActorType) by
    exact general_result (Nat.card GroupType) GroupType rfl coprime second_coprime commuting
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ _ _ target_card target_coprime target_second_coprime commuting
    apply le_antisymm (fixed_action_commutator_hull_le commuting)
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      intro element _
      have identity : element = 1 := Subsingleton.elim _ _
      rw [identity]
      exact Subgroup.one_mem _
    · let := nontrivial
      obtain ⟨parent, parent_normal, parent_nontrivial, parent_commutative, first_invariant,
        second_invariant, minimal⟩ := solvable_minimal_invariant_normal_exists
          (ActorType := ActorType) (SecondActorType := SecondActorType) (GroupType := TargetType)
      let := parent_normal
      let := parent_commutative
      let _parentCommGroup : CommGroup parent := { parent.toGroup with mul_comm := mul_comm' }
      let _firstParentAction := invariantSubgroupAction parent first_invariant
      let _secondParentAction := invariantSubgroupAction parent second_invariant
      let _firstQuotientAction := invariantQuotientAction parent first_invariant
      let _secondQuotientAction := invariantQuotientAction parent second_invariant
      have parent_commuting := commuting_subgroup_actions parent first_invariant second_invariant commuting
      have quotient_commuting := commuting_quotient_actions parent first_invariant second_invariant commuting
      have parent_coprime : Nat.Coprime prime (Nat.card parent) :=
        target_coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card parent)
      have quotient_coprime : Nat.Coprime prime (Nat.card (TargetType ⧸ parent)) :=
        target_coprime.of_dvd_right (Subgroup.card_quotient_dvd_card parent)
      have quotient_second_coprime : Nat.Coprime actionPrime (Nat.card (TargetType ⧸ parent)) :=
        target_second_coprime.of_dvd_right (Subgroup.card_quotient_dvd_card parent)
      have quotient_smaller : Nat.card (TargetType ⧸ parent) < order := by
        rw [← target_card, parent.card_eq_card_quotient_mul_card_subgroup]
        have parent_large : 1 < Nat.card parent := by
          have positive : 0 < Nat.card parent := Nat.card_pos
          have not_one : Nat.card parent ≠ 1 := by
            intro same_card
            exact parent_nontrivial (Subgroup.card_eq_one.mp same_card)
          omega
        have quotient_positive : 0 < Nat.card (TargetType ⧸ parent) := Nat.card_pos
        nlinarith
      have quotient_generated := induction_hypothesis (Nat.card (TargetType ⧸ parent)) quotient_smaller
        (TargetType ⧸ parent) rfl quotient_coprime quotient_second_coprime quotient_commuting
      have parent_generated := abelian_fixed_action_commutator_hull prime prime_prime actor_pgroup
        parent_coprime parent_commuting
      have parent_hull_le := fixed_action_commutator_hull_map_le parent.subtype
        (fun _ _ => rfl) (fun _ _ => rfl) parent_commuting commuting
      have parent_commutators_le : invariantActionCommutator parent second_invariant ≤
          fixedActionCommutatorHull commuting := by
        rw [parent_generated] at parent_hull_le
        exact parent_hull_le
      let projection := QuotientGroup.mk' parent
      have projection_kernel_coprime : Nat.Coprime prime (Nat.card projection.ker) := by
        simpa only [projection, QuotientGroup.ker_mk'] using parent_coprime
      have projected_hull := fixed_action_commutator_hull_map_eq prime prime_prime actor_pgroup
        projection (QuotientGroup.mk'_surjective parent) projection_kernel_coprime
        (invariant_quotient_equivariant parent first_invariant)
        (invariant_quotient_equivariant parent second_invariant) commuting quotient_commuting
      have projected_commutators := action_commutator_map_surjective projection
        (QuotientGroup.mk'_surjective parent) (invariant_quotient_equivariant parent second_invariant)
      have projected_equal : (actionCommutator (ActorType := SecondActorType) (GroupType := TargetType)).map
          projection = (fixedActionCommutatorHull commuting).map projection := by
        rw [projected_commutators, projected_hull, quotient_generated]
      have contained : actionCommutator (ActorType := SecondActorType) (GroupType := TargetType) ≤
          fixedActionCommutatorHull commuting ⊔ parent := by
        have image_le := Subgroup.map_le_iff_le_comap.mp projected_equal.le
        rw [Subgroup.comap_map_eq] at image_le
        simpa only [projection, QuotientGroup.ker_mk'] using image_le
      exact action_commutator_le_of_minimal_abelian_extension actionPrime action_prime second_pgroup
        target_second_coprime commuting parent first_invariant second_invariant minimal
        (fixedActionCommutatorHull commuting) (fixed_action_commutator_hull_second_invariant commuting)
        contained parent_commutators_le

end CFSG.SignalizerFunctor.Helpers
