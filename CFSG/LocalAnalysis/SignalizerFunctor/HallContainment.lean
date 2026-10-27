module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantFusion
public import CFSG.LocalAnalysis.SignalizerFunctor.ComplementConjugacy
public import CFSG.LocalAnalysis.SignalizerFunctor.ComplementRestriction

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem prime_subgroup_contained_in_conjugate_complement
    {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
    (primes : Set ℕ) (normal complement subgroup : Subgroup GroupType) [normal.Normal]
    (commutative : IsMulCommutative normal)
    (normal_supported : primeSupported primesᶜ (Nat.card normal))
    (subgroup_supported : primeSupported primes (Nat.card subgroup))
    (complementary : normal.IsComplement' complement) :
    ∃ element : normal, subgroup ≤ conjugateSubgroup element.val complement := by
  let parent := normal ⊔ subgroup
  let normalInternal := normal.subgroupOf parent
  let subgroupInternal := subgroup.subgroupOf parent
  let complementInternal := complement.subgroupOf parent
  have disjoint : Disjoint normal subgroup := Subgroup.disjoint_of_coprime_natCard
    (prime_supported_coprime primes subgroup_supported normal_supported).symm
  have subgroup_complementary := normal_subgroupOf_sup_complement normal subgroup disjoint
  have complement_complementary := complement_restriction normal complement parent complementary
    le_sup_left
  let : normalInternal.Normal := inferInstance
  have internal_normal_supported : primeSupported primesᶜ (Nat.card normalInternal) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show normal ≤ parent from le_sup_left)).toEquiv]
    exact normal_supported
  have internal_subgroup_supported : primeSupported primes (Nat.card subgroupInternal) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show subgroup ≤ parent from le_sup_right)).toEquiv]
    exact subgroup_supported
  have internal_coprime : Nat.Coprime (Nat.card normalInternal) normalInternal.index := by
    rw [subgroup_complementary.symm.index_eq_card]
    exact (prime_supported_coprime primes internal_subgroup_supported internal_normal_supported).symm
  obtain ⟨element, conjugates⟩ := abelian_normal_complements_conjugate normalInternal
    subgroupInternal complementInternal (commutative_subgroupOf parent normal commutative)
    internal_coprime subgroup_complementary complement_complementary
  have mapped_equal := congrArg (fun internal : Subgroup parent => internal.map parent.subtype)
    conjugates
  rw [conjugate_subgroup_map,
    Subgroup.map_subgroupOf_eq_of_le (show subgroup ≤ parent from le_sup_right)] at mapped_equal
  change conjugateSubgroup element.val.val subgroup = complementInternal.map parent.subtype
    at mapped_equal
  have conjugate_le : conjugateSubgroup element.val.val subgroup ≤ complement := by
    rw [mapped_equal]
    rintro value ⟨representative, member, rfl⟩
    exact member
  have inverse_le := Subgroup.map_mono
    (f := (MulAut.conj element.val.val⁻¹).toMonoidHom) conjugate_le
  change conjugateSubgroup element.val.val⁻¹ (conjugateSubgroup element.val.val subgroup) ≤
    conjugateSubgroup element.val.val⁻¹ complement at inverse_le
  rw [conjugate_subgroup_inv_cancel] at inverse_le
  exact ⟨⟨element.val.val⁻¹, normal.inv_mem element.property⟩, inverse_le⟩

theorem solvable_hall_subgroup_containing
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [Group.IsSolvable GroupType] (primes : Set ℕ) (subgroup : Subgroup GroupType)
    (supported : primeSupported primes (Nat.card subgroup)) :
    ∃ hall : Subgroup GroupType, subgroup ≤ hall ∧ IsHallSubgroup primes hall := by
  classical
  suffices general_result : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType]
        [Group.IsSolvable TargetType], Nat.card TargetType = order →
          ∀ subgroup : Subgroup TargetType, primeSupported primes (Nat.card subgroup) →
            ∃ hall : Subgroup TargetType, subgroup ≤ hall ∧ IsHallSubgroup primes hall by
    exact general_result (Nat.card GroupType) GroupType rfl subgroup supported
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ target_card subgroup supported
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      refine ⟨⊤, le_top, ?_, ?_⟩
      · have cardinality : Nat.card (⊤ : Subgroup TargetType) = 1 := Nat.card_unique
        rw [cardinality]
        exact prime_supported_one primes
      · rw [Subgroup.index_eq_one.mpr rfl]
        exact prime_supported_one primesᶜ
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
      obtain ⟨quotientHall, quotient_contains, quotient_hall⟩ := induction_hypothesis
        (Nat.card (TargetType ⧸ normal)) quotient_smaller (TargetType ⧸ normal) rfl
        (subgroup.map projection)
        (prime_supported_of_dvd primes supported (Subgroup.card_map_dvd subgroup projection))
      let parent := quotientHall.comap projection
      have subgroup_parent : subgroup ≤ parent := by
        intro element member
        exact quotient_contains (Subgroup.mem_map_of_mem projection member)
      have parent_index : parent.index = quotientHall.index :=
        Subgroup.index_comap_of_surjective quotientHall (QuotientGroup.mk'_surjective normal)
      have parent_supported : primeSupported primesᶜ parent.index := by
        rw [parent_index]
        exact quotient_hall.2
      by_cases parent_proper : parent ≠ ⊤
      · have parent_smaller : Nat.card parent < order := by
          rw [← target_card]
          apply lt_of_le_of_ne parent.card_le_card_group
          intro equal_card
          exact parent_proper (parent.card_eq_iff_eq_top.mp equal_card)
        have internal_supported : primeSupported primes (Nat.card (subgroup.subgroupOf parent)) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe subgroup_parent).toEquiv]
          exact supported
        obtain ⟨internal, internal_contains, internal_hall⟩ := induction_hypothesis
          (Nat.card parent) parent_smaller parent rfl (subgroup.subgroupOf parent) internal_supported
        refine ⟨internal.map parent.subtype, ?_,
          hall_subgroup_trans primes parent internal internal_hall parent_supported⟩
        have mapped_contains := Subgroup.map_mono (f := parent.subtype) internal_contains
        rwa [Subgroup.map_subgroupOf_eq_of_le subgroup_parent] at mapped_contains
      · have parent_equal : parent = ⊤ := not_ne_iff.mp parent_proper
        have quotient_equal : quotientHall = ⊤ := by
          apply Subgroup.index_eq_one.mp
          rw [← parent_index, parent_equal]
          exact Subgroup.index_eq_one.mpr rfl
        have quotient_supported : primeSupported primes (Nat.card (TargetType ⧸ normal)) := by
          have cardinality := quotientHall.card_eq_iff_eq_top.mpr quotient_equal
          rw [← cardinality]
          exact quotient_hall.1
        by_cases prime_member : prime ∈ primes
        · have normal_supported : primeSupported primes (Nat.card normal) := by
            rw [normal_card]
            exact prime_supported_pow_prime primes prime rank prime_prime prime_member
          have group_supported : primeSupported primes (Nat.card TargetType) := by
            rw [← normal.card_mul_index]
            exact prime_supported_mul primes normal_supported (by
              rw [normal.index_eq_card]
              exact quotient_supported)
          refine ⟨⊤, le_top, ?_, ?_⟩
          · rw [← (⊤ : Subgroup TargetType).card_eq_iff_eq_top.mpr rfl] at group_supported
            exact group_supported
          · rw [Subgroup.index_eq_one.mpr rfl]
            exact prime_supported_one primesᶜ
        · have normal_supported : primeSupported primesᶜ (Nat.card normal) := by
            rw [normal_card]
            exact prime_supported_pow_prime primesᶜ prime rank prime_prime prime_member
          obtain ⟨hall, hall_property⟩ := solvable_hall_subgroup_exists TargetType primes
          have complementary := hall_complement_of_quotient_supported primes normal hall
            hall_property normal_supported quotient_supported
          obtain ⟨element, contained⟩ := prime_subgroup_contained_in_conjugate_complement primes
            normal hall subgroup elementary.1 normal_supported supported complementary
          exact ⟨conjugateSubgroup element.val hall, contained,
            hall_conjugate primes hall element.val hall_property⟩

end CFSG.SignalizerFunctor.Helpers
