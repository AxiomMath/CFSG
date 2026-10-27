module

public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalNormal

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

@[expose] def primeSupported (primes : Set ℕ) (order : ℕ) : Prop :=
  ∀ prime : ℕ, prime.Prime → prime ∣ order → prime ∈ primes

@[expose] def IsHallSubgroup {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (subgroup : Subgroup GroupType) : Prop :=
  primeSupported primes (Nat.card subgroup) ∧ primeSupported primesᶜ subgroup.index

theorem prime_supported_one (primes : Set ℕ) : primeSupported primes 1 := by
  intro prime prime_prime divides
  exact (prime_prime.not_dvd_one divides).elim

theorem prime_supported_mul (primes : Set ℕ) {first second : ℕ}
    (first_supported : primeSupported primes first)
    (second_supported : primeSupported primes second) : primeSupported primes (first * second) := by
  intro prime prime_prime divides
  rcases prime_prime.dvd_mul.mp divides with first_divides | second_divides
  · exact first_supported prime prime_prime first_divides
  · exact second_supported prime prime_prime second_divides

theorem prime_supported_pow_prime (primes : Set ℕ) (prime rank : ℕ)
    (prime_prime : prime.Prime) (member : prime ∈ primes) :
    primeSupported primes (prime ^ rank) := by
  intro divisor divisor_prime divides
  have prime_divides := divisor_prime.dvd_of_dvd_pow divides
  have equal := (prime_prime.dvd_iff_eq divisor_prime.ne_one).mp prime_divides
  rwa [← equal]

theorem prime_supported_coprime (primes : Set ℕ) {first second : ℕ}
    (first_supported : primeSupported primes first)
    (second_supported : primeSupported primesᶜ second) : Nat.Coprime first second := by
  apply Nat.coprime_of_dvd
  intro prime prime_prime first_divides second_divides
  exact second_supported prime prime_prime second_divides
    (first_supported prime prime_prime first_divides)

theorem hall_subgroup_trans
    {GroupType : Type groupUniverse} [Group GroupType]
    (primes : Set ℕ) (parent : Subgroup GroupType) (internal : Subgroup parent)
    (internal_hall : IsHallSubgroup primes internal)
    (parent_index : primeSupported primesᶜ parent.index) :
    IsHallSubgroup primes (internal.map parent.subtype) := by
  constructor
  · rw [Subgroup.card_map_of_injective parent.subtype_injective]
    exact internal_hall.1
  · rw [Subgroup.index_map_subtype]
    exact prime_supported_mul primesᶜ internal_hall.2 parent_index

theorem solvable_hall_subgroup_exists
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [Group.IsSolvable GroupType] (primes : Set ℕ) :
    ∃ subgroup : Subgroup GroupType, IsHallSubgroup primes subgroup := by
  classical
  suffices general_result : ∀ order : ℕ,
      ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType]
        [Group.IsSolvable TargetType], Nat.card TargetType = order →
          ∃ subgroup : Subgroup TargetType, IsHallSubgroup primes subgroup by
    exact general_result (Nat.card GroupType) GroupType rfl
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ _ target_card
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      refine ⟨⊤, ?_, ?_⟩
      · have cardinality : Nat.card (⊤ : Subgroup TargetType) = 1 := Nat.card_unique
        rw [cardinality]
        exact prime_supported_one primes
      · rw [Subgroup.index_eq_one.mpr rfl]
        exact prime_supported_one primesᶜ
    · let := nontrivial
      obtain ⟨normal, normal_normal, normal_nontrivial, _, prime, rank, prime_prime,
        rank_positive, _, normal_card⟩ := solvable_minimal_normal_exists (GroupType := TargetType)
      let := normal_normal
      have quotient_smaller : Nat.card (TargetType ⧸ normal) < order := by
        rw [← target_card, ← normal.index_eq_card]
        have normal_card_large : 1 < Nat.card normal := by
          have cardinality_positive := Nat.card_pos (α := normal)
          have not_one : Nat.card normal ≠ 1 := by
            intro equal_card
            exact normal_nontrivial ((Subgroup.eq_bot_iff_card normal).mpr equal_card)
          omega
        have product := normal.card_mul_index
        have index_positive : 0 < normal.index :=
          Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        nlinarith
      obtain ⟨quotientHall, quotient_hall⟩ := induction_hypothesis
        (Nat.card (TargetType ⧸ normal)) quotient_smaller (TargetType ⧸ normal) rfl
      let projection := QuotientGroup.mk' normal
      let parent := quotientHall.comap projection
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
        obtain ⟨internal, internal_hall⟩ := induction_hypothesis (Nat.card parent) parent_smaller
          parent rfl
        exact ⟨internal.map parent.subtype,
          hall_subgroup_trans primes parent internal internal_hall parent_supported⟩
      · have parent_equal : parent = ⊤ := not_ne_iff.mp parent_proper
        have quotient_equal : quotientHall = ⊤ := by
          apply Subgroup.index_eq_one.mp
          rw [← parent_index, parent_equal]
          exact Subgroup.index_eq_one.mpr rfl
        have quotient_supported : primeSupported primes (Nat.card (TargetType ⧸ normal)) := by
          have cardinality : Nat.card quotientHall = Nat.card (TargetType ⧸ normal) :=
            quotientHall.card_eq_iff_eq_top.mpr quotient_equal
          rw [← cardinality]
          exact quotient_hall.1
        have normal_index_supported : primeSupported primes normal.index := by
          rw [normal.index_eq_card]
          exact quotient_supported
        by_cases prime_member : prime ∈ primes
        · have normal_supported : primeSupported primes (Nat.card normal) := by
            rw [normal_card]
            exact prime_supported_pow_prime primes prime rank prime_prime prime_member
          have target_supported : primeSupported primes (Nat.card TargetType) := by
            rw [← normal.card_mul_index]
            exact prime_supported_mul primes normal_supported normal_index_supported
          refine ⟨⊤, ?_, ?_⟩
          · rw [← (⊤ : Subgroup TargetType).card_eq_iff_eq_top.mpr rfl] at target_supported
            exact target_supported
          · rw [Subgroup.index_eq_one.mpr rfl]
            exact prime_supported_one primesᶜ
        · have normal_supported : primeSupported primesᶜ (Nat.card normal) := by
            rw [normal_card]
            exact prime_supported_pow_prime primesᶜ prime rank prime_prime prime_member
          have coprime : Nat.Coprime (Nat.card normal) normal.index :=
            (prime_supported_coprime primes normal_index_supported normal_supported).symm
          obtain ⟨complement, complementary⟩ := Subgroup.exists_right_complement'_of_coprime coprime
          refine ⟨complement, ?_, ?_⟩
          · rw [← complementary.symm.index_eq_card]
            exact normal_index_supported
          · rw [complementary.index_eq_card]
            exact normal_supported

end CFSG.SignalizerFunctor.Helpers
