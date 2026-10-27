module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions
public import CFSG.LocalAnalysis.SignalizerFunctor.SimplePrimePowerConjugacyClass
public import CFSG.LocalAnalysis.SignalizerFunctor.ConjugacyClassIndices

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem simple_two_prime_order_solvable
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] [IsSimpleGroup GroupType]
    (firstPrime secondPrime : ℕ) (first_prime : firstPrime.Prime) (second_prime : secondPrime.Prime)
    (supported : ∀ divisor : ℕ, divisor.Prime → divisor ∣ Nat.card GroupType →
      divisor = firstPrime ∨ divisor = secondPrime) : Group.IsSolvable GroupType := by
  classical
  have card_ne_one : Nat.card GroupType ≠ 1 := ne_of_gt Finite.one_lt_card
  obtain ⟨prime, prime_prime, divides⟩ := Nat.exists_prime_and_dvd card_ne_one
  let : Fact prime.Prime := ⟨prime_prime⟩
  let sylow : Sylow prime GroupType := Classical.choice inferInstance
  let : Nontrivial sylow := (Subgroup.nontrivial_iff_ne_bot _).mpr (sylow.ne_bot_of_dvd_card divides)
  have center_large := sylow.isPGroup'.bot_lt_center
  obtain ⟨centralElement, central, central_ne⟩ := IsConcreteLE.exists_of_lt center_large
  have central_ne_one : (centralElement : GroupType) ≠ 1 := by
    intro equal
    apply central_ne
    rw [Subgroup.mem_bot]
    exact Subtype.ext equal
  have class_coprime := sylow_central_element_class_coprime prime prime_prime sylow centralElement central
  have class_not_divides : ¬prime ∣ (conjugacyClassFinset (centralElement : GroupType)).card :=
    prime_prime.coprime_iff_not_dvd.mp class_coprime
  let otherPrime := if prime = firstPrime then secondPrime else firstPrime
  have other_prime : otherPrime.Prime := by
    dsimp only [otherPrime]
    split_ifs
    · exact second_prime
    · exact first_prime
  have class_positive : 0 < (conjugacyClassFinset (centralElement : GroupType)).card := by
    apply Finset.card_pos.mpr
    exact ⟨centralElement, (mem_conjugacyClassFinset _ _).mpr (IsConj.refl _)⟩
  have unique : ∀ divisor : ℕ, divisor.Prime →
      divisor ∣ (conjugacyClassFinset (centralElement : GroupType)).card → divisor = otherPrime := by
    intro divisor divisor_prime divisor_divides
    have divisor_supported := supported divisor divisor_prime
      (divisor_divides.trans (conjugacyClassFinset_card_dvd_group _))
    have prime_supported := supported prime prime_prime divides
    have different : divisor ≠ prime := fun equal => class_not_divides (equal ▸ divisor_divides)
    dsimp only [otherPrime]
    split_ifs with equal
    · rcases divisor_supported with first | second
      · exact False.elim (different (first.trans equal.symm))
      · exact second
    · rcases prime_supported with first | second
      · exact False.elim (equal first)
      · rcases divisor_supported with divisor_first | divisor_second
        · exact divisor_first
        · exact False.elim (different (divisor_second.trans second.symm))
  have class_power := Nat.eq_prime_pow_of_unique_prime_dvd class_positive.ne'
    (fun divisor_prime divisor_divides => unique _ divisor_prime divisor_divides)
  have ambient_central := simple_group_prime_power_class_central GroupType otherPrime other_prime
    (conjugacyClassFinset (centralElement : GroupType)).card.primeFactorsList.length
    centralElement central_ne_one class_power
  have center_nontrivial : Subgroup.center GroupType ≠ ⊥ := by
    intro trivial
    rw [trivial, Subgroup.mem_bot] at ambient_central
    exact central_ne_one ambient_central
  have center_top : Subgroup.center GroupType = ⊤ :=
    (CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center GroupType) inferInstance).resolve_left center_nontrivial
  apply Group.isSolvable_of_comm
  intro first second
  exact Subgroup.mem_center_iff.mp (by rw [center_top]; exact Subgroup.mem_top second) first

theorem two_prime_order_solvable
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    (firstPrime secondPrime : ℕ) (first_prime : firstPrime.Prime) (second_prime : secondPrime.Prime)
    (supported : ∀ divisor : ℕ, divisor.Prime → divisor ∣ Nat.card GroupType →
      divisor = firstPrime ∨ divisor = secondPrime) : Group.IsSolvable GroupType := by
  classical
  suffices general : ∀ order : ℕ, ∀ (TargetType : Type groupUniverse) [Group TargetType] [Finite TargetType],
      Nat.card TargetType = order →
      (∀ divisor : ℕ, divisor.Prime → divisor ∣ Nat.card TargetType →
        divisor = firstPrime ∨ divisor = secondPrime) → Group.IsSolvable TargetType by
    exact general (Nat.card GroupType) GroupType rfl supported
  intro order
  induction order using Nat.strong_induction_on with
  | h order induction_hypothesis =>
    intro TargetType _ _ target_card target_supported
    rcases subsingleton_or_nontrivial TargetType with trivial | nontrivial
    · let := trivial
      infer_instance
    let := nontrivial
    by_cases exists_normal : ∃ normal : Subgroup TargetType, normal.Normal ∧ normal ≠ ⊥ ∧ normal ≠ ⊤
    · obtain ⟨normal, normal_property, normal_ne_bot, normal_ne_top⟩ := exists_normal
      let := normal_property
      have normal_smaller : Nat.card normal < order := by
        rw [← target_card]
        exact lt_of_le_of_ne normal.card_le_card_group
          (fun equal => normal_ne_top (normal.card_eq_iff_eq_top.mp equal))
      have quotient_smaller : Nat.card (TargetType ⧸ normal) < order := by
        rw [← target_card]
        exact normal_quotient_card_strict normal normal_ne_bot
      let : Group.IsSolvable normal := induction_hypothesis (Nat.card normal) normal_smaller normal rfl
        (fun divisor divisor_prime divides => target_supported divisor divisor_prime
          (divides.trans normal.card_subgroup_dvd_card))
      let : Group.IsSolvable (TargetType ⧸ normal) := induction_hypothesis
        (Nat.card (TargetType ⧸ normal)) quotient_smaller (TargetType ⧸ normal) rfl
        (fun divisor divisor_prime divides => target_supported divisor divisor_prime
          (divides.trans normal.card_quotient_dvd_card))
      exact (Group.isSolvable_iff_subgroup_quotient normal).mpr ⟨inferInstance, inferInstance⟩
    · let : IsSimpleGroup TargetType :=
        { eq_bot_or_eq_top_of_normal := fun normal normal_property => by
            by_cases trivial_normal : normal = ⊥
            · exact Or.inl trivial_normal
            · right
              by_contra proper_normal
              exact exists_normal ⟨normal, normal_property, trivial_normal, proper_normal⟩ }
      exact simple_two_prime_order_solvable TargetType firstPrime secondPrime first_prime second_prime target_supported

end CFSG.SignalizerFunctor.Helpers
