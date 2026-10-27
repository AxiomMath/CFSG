module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantFusion
public import CFSG.LocalAnalysis.SignalizerFunctor.ComplementConjugacy
public import CFSG.LocalAnalysis.SignalizerFunctor.HallTransport

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem quotient_map_eq_top_of_sup_normal_eq_top
    {GroupType : Type groupUniverse} [Group GroupType]
    (normal subgroup : Subgroup GroupType) [normal.Normal]
    (whole : subgroup ⊔ normal = ⊤) : subgroup.map (QuotientGroup.mk' normal) = ⊤ := by
  apply Subgroup.index_eq_one.mp
  rw [Subgroup.index_map, QuotientGroup.ker_mk', whole,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective normal)]
  simp

theorem solvable_hall_subgroups_conjugate
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [Group.IsSolvable GroupType] (primes : Set ℕ)
    (first second : Subgroup GroupType)
    (first_hall : IsHallSubgroup primes first) (second_hall : IsHallSubgroup primes second) :
    ∃ element : GroupType, conjugateSubgroup element first = second := by
  classical
  suffices general_result : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType]
        [Group.IsSolvable TargetType], Nat.card TargetType = order →
          ∀ first second : Subgroup TargetType, IsHallSubgroup primes first →
            IsHallSubgroup primes second →
              ∃ element : TargetType, conjugateSubgroup element first = second by
    exact general_result (Nat.card GroupType) GroupType rfl first second first_hall second_hall
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ target_card first second first_hall second_hall
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      refine ⟨1, ?_⟩
      rw [conjugate_subgroup_one]
      exact Subsingleton.elim _ _
    · let := nontrivial
      obtain ⟨normal, normal_normal, normal_nontrivial, _, prime, rank, prime_prime,
        _, elementary, normal_card⟩ := solvable_minimal_normal_exists (GroupType := TargetType)
      let := normal_normal
      have quotient_smaller : Nat.card (TargetType ⧸ normal) < order := by
        rw [← target_card, ← normal.index_eq_card]
        have cardinality_positive := Nat.card_pos (α := normal)
        have not_one : Nat.card normal ≠ 1 := by
          intro equal_card
          exact normal_nontrivial ((Subgroup.eq_bot_iff_card normal).mpr equal_card)
        have normal_large : 1 < Nat.card normal := by omega
        have product := normal.card_mul_index
        have index_positive : 0 < normal.index := Nat.pos_of_ne_zero
          Subgroup.index_ne_zero_of_finite
        nlinarith
      let projection := QuotientGroup.mk' normal
      have projection_surjective := QuotientGroup.mk'_surjective normal
      obtain ⟨quotientElement, quotient_conjugates⟩ := induction_hypothesis
        (Nat.card (TargetType ⧸ normal)) quotient_smaller (TargetType ⧸ normal) rfl
        (first.map projection) (second.map projection)
        (hall_map_surjective primes projection projection_surjective first first_hall)
        (hall_map_surjective primes projection projection_surjective second second_hall)
      obtain ⟨element, element_maps⟩ := projection_surjective quotientElement
      let moved := conjugateSubgroup element first
      have moved_hall := hall_conjugate primes first element first_hall
      have mapped_equal : moved.map projection = second.map projection := by
        rw [conjugate_subgroup_map, element_maps]
        exact quotient_conjugates
      have sup_equal := sup_normal_eq_of_quotient_map_eq normal moved second mapped_equal
      let parent := moved ⊔ normal
      have moved_le : moved ≤ parent := le_sup_left
      have second_le : second ≤ parent := by
        change second ≤ moved ⊔ normal
        rw [sup_equal]
        exact le_sup_left
      by_cases parent_proper : parent ≠ ⊤
      · have parent_smaller : Nat.card parent < order := by
          rw [← target_card]
          apply lt_of_le_of_ne parent.card_le_card_group
          intro equal_card
          exact parent_proper (parent.card_eq_iff_eq_top.mp equal_card)
        obtain ⟨internalElement, conjugates⟩ := induction_hypothesis (Nat.card parent)
          parent_smaller parent rfl (moved.subgroupOf parent) (second.subgroupOf parent)
          (hall_subgroupOf primes moved parent moved_le moved_hall)
          (hall_subgroupOf primes second parent second_le second_hall)
        have mapped_conjugates := congrArg (fun internal : Subgroup parent =>
          internal.map parent.subtype) conjugates
        rw [conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le moved_le,
          Subgroup.map_subgroupOf_eq_of_le second_le] at mapped_conjugates
        refine ⟨internalElement.val * element, ?_⟩
        rw [← conjugate_subgroup_mul]
        exact mapped_conjugates
      · have parent_whole : moved ⊔ normal = ⊤ := not_ne_iff.mp parent_proper
        have second_whole : second ⊔ normal = ⊤ := by rwa [sup_equal] at parent_whole
        have quotient_whole := quotient_map_eq_top_of_sup_normal_eq_top normal second second_whole
        have quotient_hall := hall_map_surjective primes projection projection_surjective
          second second_hall
        have quotient_supported : primeSupported primes (Nat.card (TargetType ⧸ normal)) := by
          have cardinality : Nat.card (second.map projection) = Nat.card (TargetType ⧸ normal) :=
            (second.map projection).card_eq_iff_eq_top.mpr quotient_whole
          rw [← cardinality]
          exact quotient_hall.1
        have normal_index_supported : primeSupported primes normal.index := by
          rw [normal.index_eq_card]
          exact quotient_supported
        by_cases prime_member : prime ∈ primes
        · have normal_supported : primeSupported primes (Nat.card normal) := by
            rw [normal_card]
            exact prime_supported_pow_prime primes prime rank prime_prime prime_member
          have group_supported : primeSupported primes (Nat.card TargetType) := by
            rw [← normal.card_mul_index]
            exact prime_supported_mul primes normal_supported normal_index_supported
          refine ⟨1, ?_⟩
          rw [conjugate_subgroup_one, hall_eq_top_of_group_supported primes first first_hall
            group_supported, hall_eq_top_of_group_supported primes second second_hall group_supported]
        · have normal_supported : primeSupported primesᶜ (Nat.card normal) := by
            rw [normal_card]
            exact prime_supported_pow_prime primesᶜ prime rank prime_prime prime_member
          have moved_complementary := hall_complement_of_quotient_supported primes normal moved
            moved_hall normal_supported quotient_supported
          have second_complementary := hall_complement_of_quotient_supported primes normal second
            second_hall normal_supported quotient_supported
          have coprime : Nat.Coprime (Nat.card normal) normal.index :=
            (prime_supported_coprime primes normal_index_supported normal_supported).symm
          obtain ⟨normalElement, conjugates⟩ := abelian_normal_complements_conjugate normal moved
            second elementary.1 coprime moved_complementary second_complementary
          refine ⟨normalElement.val * element, ?_⟩
          rw [← conjugate_subgroup_mul]
          exact conjugates

end CFSG.SignalizerFunctor.Helpers
