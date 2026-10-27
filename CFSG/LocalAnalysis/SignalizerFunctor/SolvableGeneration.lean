module

public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.GenerationExtension
public import Mathlib.GroupTheory.Schreier

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem solvable_cyclic_quotient_generation
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [Group.IsSolvable GroupType] [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    (⨆ (actorSubgroup : Subgroup ActorType) (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
      FixedPoints.subgroup actorSubgroup GroupType) = ⊤ := by
  classical
  suffices general_result : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType]
        [Group.IsSolvable TargetType] [MulDistribMulAction ActorType TargetType],
        Nat.card TargetType = order → Nat.Coprime prime (Nat.card TargetType) →
          (⨆ (actorSubgroup : Subgroup ActorType)
              (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
            FixedPoints.subgroup actorSubgroup TargetType) = ⊤ by
    exact general_result (Nat.card GroupType) GroupType rfl coprime
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ _ target_card target_coprime
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      apply top_unique
      intro element _
      have element_one : element = 1 := Subsingleton.elim _ _
      rw [element_one]
      exact Subgroup.one_mem _
    · let := nontrivial
      let subgroup := commutator TargetType
      have invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
          actorElement • element ∈ subgroup := by
        intro actorElement element member
        have map_le : subgroup ≤ subgroup.comap
            (MulDistribMulAction.toMulEquiv TargetType actorElement).toMonoidHom :=
          Subgroup.characteristic_iff_le_comap.mp inferInstance _
        exact map_le member
      let _subgroupAction := invariantSubgroupAction subgroup invariant
      let _quotientAction := invariantQuotientAction subgroup invariant
      let _quotientCommGroup : CommGroup (TargetType ⧸ subgroup) :=
        inferInstanceAs (CommGroup (Abelianization TargetType))
      have subgroup_coprime : Nat.Coprime prime (Nat.card subgroup) :=
        target_coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card subgroup)
      have quotient_coprime : Nat.Coprime prime (Nat.card (TargetType ⧸ subgroup)) :=
        target_coprime.of_dvd_right (Subgroup.card_quotient_dvd_card subgroup)
      have subgroup_smaller : Nat.card subgroup < order := by
        rw [← target_card]
        apply lt_of_le_of_ne subgroup.card_le_card_group
        intro equal_card
        exact (Group.IsSolvable.commutator_lt_top_of_nontrivial TargetType).ne
          (subgroup.card_eq_iff_eq_top.mp equal_card)
      have subgroup_generated := induction_hypothesis (Nat.card subgroup)
        subgroup_smaller subgroup rfl subgroup_coprime
      have quotient_generated := abelian_cyclic_quotient_generation prime prime_prime
        ActorType actor_pgroup (TargetType ⧸ subgroup) quotient_coprime
      exact cyclic_quotient_generation_of_normal_extension prime prime_prime
        ActorType actor_pgroup TargetType subgroup invariant subgroup_coprime
        subgroup_generated quotient_generated

end CFSG.SignalizerFunctor.Helpers
