module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProjectiveTwoFixedPoints
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryProjectiveRank

public section

universe fieldUniverse vectorUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType] [IsAlgClosed FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]
variable [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
variable {ActorType : Type actorUniverse} [Group ActorType] [Finite ActorType]

omit [Finite ActorType] in
theorem abelian_coprime_pgroup_projective_invariant_pair
    (dimension : Module.finrank FieldType VectorType = 2)
    (characteristic : ℕ) (characteristic_prime : characteristic.Prime) [CharP FieldType characteristic]
    (prime : ℕ) (prime_prime : prime.Prime) (different : prime ≠ characteristic)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (pgroup : IsPGroup prime ActorType)
    (abelian : ∀ first second : ActorType,
      Commute (projectiveLinearAction (action first)) (projectiveLinearAction (action second)))
    (nontrivial : ∃ actor : ActorType, projectiveLinearAction (action actor) ≠ 1) :
    ∃ first second : Projectivization FieldType VectorType, first ≠ second ∧
      ∀ actor : ActorType, ∀ point : Projectivization FieldType VectorType,
        projectiveLinearAction (action actor) point ∈
          ({first, second} : Set (Projectivization FieldType VectorType)) ↔
        point ∈ ({first, second} : Set (Projectivization FieldType VectorType)) := by
  obtain ⟨actor, actor_nontrivial⟩ := nontrivial
  obtain ⟨exponent, power⟩ := pgroup actor
  have coprime : ¬characteristic ∣ prime ^ exponent := by
    intro divides
    exact different (prime_prime.dvd_iff_eq characteristic_prime.ne_one |>.mp
      (characteristic_prime.dvd_of_dvd_pow divides))
  have action_power : action actor ^ (prime ^ exponent) = 1 := by rw [← map_pow, power, map_one]
  obtain ⟨first, second, distinct, fixed_exact⟩ := coprime_order_projective_fixed_exactly_two
    dimension characteristic (action actor) (prime ^ exponent) coprime action_power actor_nontrivial
  refine ⟨first, second, distinct, ?_⟩
  intro other point
  have fixed_invariant := commuting_permutation_preserves_fixed
    (projectiveLinearAction (action actor)) (projectiveLinearAction (action other)) (abelian actor other) point
  simpa only [fixed_exact, Set.mem_insert_iff, Set.mem_singleton_iff] using fixed_invariant

theorem coprime_elementary_projective_rank_bound
    (dimension : Module.finrank FieldType VectorType = 2)
    (characteristic : ℕ) (characteristic_prime : characteristic.Prime) [CharP FieldType characteristic]
    (prime : ℕ) (prime_prime : prime.Prime) (different : prime ≠ characteristic)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (pgroup : IsPGroup prime ActorType)
    (abelian : ∀ first second : ActorType,
      Commute (projectiveLinearAction (action first)) (projectiveLinearAction (action second)))
    (exponent : ∀ actor : ActorType, projectiveLinearAction (action actor) ^ prime = 1)
    (nontrivial : ∃ actor : ActorType, projectiveLinearAction (action actor) ≠ 1) :
    Nat.card (projectiveLinearAction.comp action).range = prime ∨
      (prime = 2 ∧ Nat.card (projectiveLinearAction.comp action).range = 4) := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  let projective := projectiveLinearAction.comp action
  let _finite : Finite projective.range :=
    Finite.of_surjective projective.rangeRestrict projective.rangeRestrict_surjective
  have image_pgroup := pgroup.of_surjective projective.rangeRestrict projective.rangeRestrict_surjective
  have image_nontrivial : Nat.card projective.range ≠ 1 := by
    intro cardinality
    have trivial := Subgroup.card_eq_one.mp cardinality
    obtain ⟨actor, actor_nontrivial⟩ := nontrivial
    have member : projective actor ∈ projective.range := ⟨actor, rfl⟩
    rw [trivial, Subgroup.mem_bot] at member
    exact actor_nontrivial member
  obtain ⟨first, second, distinct, invariant⟩ := abelian_coprime_pgroup_projective_invariant_pair
    dimension characteristic characteristic_prime prime prime_prime different action pgroup abelian nontrivial
  by_cases prime_two : prime = 2
  · have bound := elementary_projective_two_set_card_bound dimension prime prime_prime action exponent
      first second distinct invariant
    obtain ⟨rank, card⟩ := image_pgroup.exists_card_eq
    change Nat.card projective.range ≤ 2 * prime at bound
    rw [prime_two] at card bound
    have rank_bound : rank ≤ 2 := by
      by_contra rank_large
      have power_bound : 2 ^ 3 ≤ 2 ^ rank := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    interval_cases rank
    · simp only [pow_zero] at card
      exact (image_nontrivial card).elim
    · left
      simpa only [pow_one, prime_two] using card
    · right
      exact ⟨prime_two, card⟩
  · let _cyclic := odd_prime_elementary_projective_two_set_cyclic dimension prime prime_prime prime_two
      action exponent first second distinct invariant
    have image_exponent : ∀ actor : projective.range, actor ^ prime = 1 := by
      intro actor
      obtain ⟨source, source_eq⟩ := actor.property
      apply Subtype.ext
      change actor.val ^ prime = 1
      rw [← source_eq]
      exact exponent source
    have divides := cyclic_prime_exponent_card_dvd prime image_exponent
    left
    exact (prime_prime.eq_one_or_self_of_dvd _ divides).resolve_left image_nontrivial

end CFSG.SignalizerFunctor.Helpers
