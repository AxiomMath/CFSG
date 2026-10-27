module

public import CFSG.LocalAnalysis.SignalizerFunctor.OnePrimeCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem subgroup_product_reverse_whole (first second : Subgroup GroupType)
    (whole : subgroupProduct first second = Set.univ) : subgroupProduct second first = Set.univ := by
  apply (subgroup_product_eq_univ_iff second first).mpr
  intro element
  obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ :=
    (subgroup_product_eq_univ_iff first second).mp whole element⁻¹
  refine ⟨secondElement⁻¹, second.inv_mem second_member, firstElement⁻¹, first.inv_mem first_member, ?_⟩
  simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv product

theorem sylow_lift_of_coprime_index (prime : ℕ) (prime_prime : prime.Prime)
    (subgroup : Subgroup GroupType) (index_coprime : Nat.Coprime prime subgroup.index)
    (sylow : Sylow prime subgroup) :
    ∃ lifted : Sylow prime GroupType,
      (lifted : Subgroup GroupType) = (sylow : Subgroup subgroup).map subgroup.subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let embedded := (sylow : Subgroup subgroup).map subgroup.subtype
  have index_not_dvd : ¬ prime ∣ embedded.index := by
    rw [Subgroup.index_map_subtype]
    exact prime_prime.not_dvd_mul sylow.not_dvd_index (prime_prime.coprime_iff_not_dvd.mp index_coprime)
  have pgroup : IsPGroup prime embedded := sylow.isPGroup'.map subgroup.subtype
  exact ⟨pgroup.toSylow index_not_dvd, IsPGroup.toSylow_coe _ _⟩

theorem hall_product_orders (prime : ℕ) (prime_prime : prime.Prime)
    (complement sylowFactor : Subgroup GroupType)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime sylowFactor)
    (whole : subgroupProduct complement sylowFactor = Set.univ) :
    complement ⊓ sylowFactor = ⊥ ∧
      Nat.card GroupType = Nat.card complement * Nat.card sylowFactor ∧
      complement.index = Nat.card sylowFactor ∧
      ∃ sylow : Sylow prime GroupType, (sylow : Subgroup GroupType) = sylowFactor := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have intersection_trivial : complement ⊓ sylowFactor = ⊥ := by
    have intersection_pgroup : IsPGroup prime (complement ⊓ sylowFactor : Subgroup GroupType) :=
      factor_pgroup.to_le inf_le_right
    have intersection_coprime : Nat.Coprime prime (Nat.card (complement ⊓ sylowFactor : Subgroup GroupType)) :=
      complement_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    rcases intersection_pgroup.card_eq_or_dvd with card_eq | divides
    · exact (Subgroup.eq_bot_iff_card _).mpr card_eq
    · exact (prime_prime.coprime_iff_not_dvd.mp intersection_coprime divides).elim
  have cardinality := subgroup_product_cardinality complement sylowFactor
  rw [whole, Nat.card_univ, intersection_trivial, Subgroup.card_bot, mul_one] at cardinality
  have index_eq : complement.index = Nat.card sylowFactor := by
    have index_formula := complement.card_mul_index
    rw [← cardinality] at index_formula
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos index_formula
  have factor_index_coprime : Nat.Coprime prime sylowFactor.index := by
    have index_formula := sylowFactor.card_mul_index
    rw [← cardinality, mul_comm (Nat.card complement)] at index_formula
    have index_card := Nat.eq_of_mul_eq_mul_left Nat.card_pos index_formula
    rwa [index_card]
  exact ⟨intersection_trivial, cardinality.symm, index_eq,
    factor_pgroup.toSylow (prime_prime.coprime_iff_not_dvd.mp factor_index_coprime), IsPGroup.toSylow_coe _ _⟩

omit [Finite GroupType] in
theorem normalized_subgroup_le_core_of_product (complement factor target : Subgroup GroupType)
    (whole : subgroupProduct complement factor = Set.univ) (target_le : target ≤ complement)
    (normalized : factor ≤ Subgroup.normalizer (target : Set GroupType)) : target ≤ complement.normalCore := by
  rw [Subgroup.normalCore_eq_iInf_comap_conj]
  apply le_iInf
  intro conjugator element member
  obtain ⟨complementElement, complement_member, factorElement, factor_member, product⟩ :=
    (subgroup_product_eq_univ_iff complement factor).mp whole conjugator
  have conjugated_member := Subgroup.le_normalizer_iff.mp normalized factorElement factor_member element member
  have ambient_member := complement.mul_mem
    (complement.mul_mem complement_member (target_le conjugated_member)) (complement.inv_mem complement_member)
  change conjugator * element * conjugator⁻¹ ∈ complement
  rw [← product]
  have equal : (complementElement * factorElement) * element * (complementElement * factorElement)⁻¹ =
      complementElement * (factorElement * element * factorElement⁻¹) * complementElement⁻¹ := by group
  rwa [equal]

theorem hall_product_normalized_prime_subgroup_le_complement
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (distinct : groupPrime ≠ prime)
    (complement factor target : Subgroup GroupType)
    (index_eq : complement.index = Nat.card factor) (factor_pgroup : IsPGroup prime factor)
    (whole : subgroupProduct complement factor = Set.univ)
    (target_pgroup : IsPGroup groupPrime target)
    (normalized : factor ≤ Subgroup.normalizer (target : Set GroupType)) : target ≤ complement := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let complementSylow : Sylow groupPrime complement := Classical.choice inferInstance
  have index_coprime : Nat.Coprime groupPrime complement.index := by
    rw [index_eq]
    exact prime_coprime_pgroup_card groupPrime prime groupPrime_prime prime_prime distinct factor_pgroup
  obtain ⟨liftedSylow, lifted_eq⟩ := sylow_lift_of_coprime_index groupPrime groupPrime_prime complement
    index_coprime complementSylow
  obtain ⟨targetSylow, target_le⟩ := target_pgroup.exists_le_sylow
  obtain ⟨conjugator, conjugates⟩ := MulAction.exists_smul_eq GroupType liftedSylow targetSylow
  have subgroup_eq : conjugateSubgroup conjugator (liftedSylow : Subgroup GroupType) = targetSylow :=
    congrArg (fun sylow : Sylow groupPrime GroupType => (sylow : Subgroup GroupType)) conjugates
  have conjugate_le := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom)
    (show (liftedSylow : Subgroup GroupType) ≤ complement from by rw [lifted_eq]; exact Subgroup.map_subtype_le _)
  change conjugateSubgroup conjugator (liftedSylow : Subgroup GroupType) ≤
    conjugateSubgroup conjugator complement at conjugate_le
  rw [subgroup_eq] at conjugate_le
  have target_conjugate := target_le.trans conjugate_le
  obtain ⟨factorElement, factor_member, complementElement, complement_member, product⟩ :=
    (subgroup_product_eq_univ_iff factor complement).mp (subgroup_product_reverse_whole complement factor whole) conjugator
  have complement_preserved := conjugate_subgroup_eq_of_mem complementElement complement complement_member
  rw [← product, ← conjugate_subgroup_mul, complement_preserved] at target_conjugate
  have inverse_le := Subgroup.map_mono (f := (MulAut.conj factorElement⁻¹).toMonoidHom) target_conjugate
  change conjugateSubgroup factorElement⁻¹ target ≤
    conjugateSubgroup factorElement⁻¹ (conjugateSubgroup factorElement complement) at inverse_le
  have target_preserved : conjugateSubgroup factorElement⁻¹ target = target :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalized (factor.inv_mem factor_member))
  rwa [target_preserved, conjugate_subgroup_inv_cancel] at inverse_le

theorem hall_product_normalized_complement_le_core
    (prime : ℕ) (prime_prime : prime.Prime) (complement factor target : Subgroup GroupType)
    (complement_coprime : Nat.Coprime prime (Nat.card complement))
    (factor_pgroup : IsPGroup prime factor) (whole : subgroupProduct complement factor = Set.univ)
    (target_coprime : Nat.Coprime prime (Nat.card target))
    (normalized : factor ≤ Subgroup.normalizer (target : Set GroupType)) : target ≤ complement.normalCore := by
  have orders := hall_product_orders prime prime_prime complement factor complement_coprime factor_pgroup whole
  let _action := conjugationAction factor target normalized
  have target_le : target ≤ complement := by
    have contains_sylows : ∀ groupPrime : ℕ, groupPrime.Prime →
        ∃ sylow : Sylow groupPrime target, (sylow : Subgroup target) ≤ complement.subgroupOf target := by
      intro groupPrime groupPrime_prime
      by_cases distinct : groupPrime = prime
      · subst groupPrime
        let : Fact prime.Prime := ⟨prime_prime⟩
        let sylow : Sylow prime target := Classical.choice inferInstance
        have trivial : (sylow : Subgroup target) = ⊥ := by
          rcases sylow.isPGroup'.card_eq_or_dvd with cardinality | divides
          · exact (Subgroup.eq_bot_iff_card _).mpr cardinality
          · exact (prime_prime.coprime_iff_not_dvd.mp target_coprime
              (divides.trans (sylow : Subgroup target).card_subgroup_dvd_card)).elim
        exact ⟨sylow, by rw [trivial]; exact bot_le⟩
      · obtain ⟨sylow, normalized_sylow⟩ := normalized_subgroup_invariant_sylow prime groupPrime prime_prime
          groupPrime_prime factor target factor_pgroup normalized target_coprime
        have embedded_le := hall_product_normalized_prime_subgroup_le_complement prime groupPrime prime_prime
          groupPrime_prime distinct complement factor ((sylow : Subgroup target).map target.subtype)
          orders.2.2.1 factor_pgroup whole (sylow.isPGroup'.map target.subtype) normalized_sylow
        refine ⟨sylow, ?_⟩
        intro element member
        exact embedded_le (Subgroup.mem_map_of_mem target.subtype member)
    have internal_top := eq_top_of_sylow_containment (complement.subgroupOf target) contains_sylows
    intro element member
    have internal_member : (⟨element, member⟩ : target) ∈ complement.subgroupOf target := by
      rw [internal_top]
      trivial
    exact internal_member
  exact normalized_subgroup_le_core_of_product complement factor target whole target_le normalized

end CFSG.SignalizerFunctor.Helpers
