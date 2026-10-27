module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem pgroup_sylow_of_card_eq (prime : ℕ) (prime_prime : prime.Prime)
    (subgroup : Subgroup GroupType) (pgroup : IsPGroup prime subgroup)
    (sylow : Sylow prime GroupType)
    (cardinality : Nat.card subgroup = Nat.card (sylow : Subgroup GroupType)) :
    ∃ result : Sylow prime GroupType, (result : Subgroup GroupType) = subgroup := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have index_equal : subgroup.index = (sylow : Subgroup GroupType).index := by
    have first_product := subgroup.card_mul_index
    have second_product := (sylow : Subgroup GroupType).card_mul_index
    rw [cardinality] at first_product
    nlinarith [Nat.card_pos (α := (sylow : Subgroup GroupType))]
  have not_divides : ¬ prime ∣ subgroup.index := by
    rw [index_equal]
    exact sylow.not_dvd_index
  exact ⟨pgroup.toSylow not_divides, IsPGroup.toSylow_coe pgroup not_divides⟩

theorem signalizer_prime_local_sylow
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (values_invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (maximalSubgroup target : Subgroup GroupType)
    (maximal : Maximal (signalizerPrimeCompatible prime rank groupPrime actor values)
      maximalSubgroup)
    (target_compatible : signalizerCompatible prime rank actor values target) :
    ∃ element : signalizerCommonFixed prime rank actor values,
      ∃ sylow : Sylow groupPrime target,
        (sylow : Subgroup target).map target.subtype =
          conjugateSubgroup element.val maximalSubgroup ⊓ target ∧
        actor ≤ Subgroup.normalizer
          ((conjugateSubgroup element.val maximalSubgroup ⊓ target : Subgroup GroupType) :
            Set GroupType) := by
  classical
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_add]
    exact Nat.le_mul_of_pos_right _ (pow_pos prime_prime.pos 2)
  have target_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values values_coprime target target_compatible.1 target_compatible.2
  let _action := conjugationAction actor target target_compatible.1
  obtain ⟨sylow, fixed⟩ := invariant_sylow_exists prime groupPrime prime_prime groupPrime_prime
    (elementary_abelian_isPGroup prime actor elementary) target_coprime
  let embedded := (sylow : Subgroup target).map target.subtype
  have embedded_le : embedded ≤ target := by
    rintro element ⟨representative, _, rfl⟩
    exact representative.property
  have embedded_normalized : actor ≤ Subgroup.normalizer (embedded : Set GroupType) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actorElement actor_member element member
    obtain ⟨representative, representative_member, rfl⟩ := member
    have image_fixed : (⟨actorElement, actor_member⟩ : actor) •
        (sylow : Subgroup target) = sylow := by
      rw [← Sylow.pointwise_smul_def, fixed]
    refine ⟨(⟨actorElement, actor_member⟩ : actor) • representative, ?_, rfl⟩
    rw [← image_fixed]
    exact Subgroup.smul_mem_pointwise_smul representative
      (⟨actorElement, actor_member⟩ : actor) _ representative_member
  have embedded_compatible : signalizerPrimeCompatible prime rank groupPrime actor values
      embedded := ⟨signalizer_compatible_of_le prime rank actor values target_compatible
        embedded_le embedded_normalized, sylow.isPGroup'.map target.subtype⟩
  obtain ⟨other, embedded_contains, other_maximal⟩ :=
    Finite.exists_le_maximal (p := signalizerPrimeCompatible prime rank groupPrime actor values)
      embedded_compatible
  obtain ⟨element, conjugates⟩ := signalizer_prime_transitivity prime rank groupPrime prime_prime
    groupPrime_prime distinct actor elementary large values values_coprime values_invariant
    balanced maximalSubgroup other maximal other_maximal
  have subgroupOf_equal : (other ⊓ target).subgroupOf target = other.subgroupOf target := by
    ext element
    exact and_iff_left element.property
  have internal_pgroup : IsPGroup groupPrime (other.subgroupOf target) := by
    rw [← subgroupOf_equal]
    exact (other_maximal.prop.2.to_le (show other ⊓ target ≤ other from inf_le_left)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (show other ⊓ target ≤ target from inf_le_right)).symm
  have internal_contains : (sylow : Subgroup target) ≤ other.subgroupOf target := by
    intro representative member
    exact embedded_contains (Subgroup.mem_map_of_mem target.subtype member)
  have internal_equal := sylow.is_maximal' internal_pgroup internal_contains
  have ambient_equal := congrArg (fun internal : Subgroup target => internal.map target.subtype)
    internal_equal
  rw [← subgroupOf_equal, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at ambient_equal
  refine ⟨element, sylow, ?_, ?_⟩
  · rw [conjugates]
    exact ambient_equal.symm
  · rw [conjugates]
    exact normalizer_inf_of_le actor other target other_maximal.prop.1.1 target_compatible.1

theorem signalizer_prime_local_sylow_of_common_normalizes
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (values_invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (maximalSubgroup target : Subgroup GroupType)
    (maximal : Maximal (signalizerPrimeCompatible prime rank groupPrime actor values)
      maximalSubgroup)
    (target_compatible : signalizerCompatible prime rank actor values target)
    (common_normalizes : signalizerCommonFixed prime rank actor values ≤
      Subgroup.normalizer (target : Set GroupType)) :
    ∃ sylow : Sylow groupPrime target,
      (sylow : Subgroup target).map target.subtype = maximalSubgroup ⊓ target ∧
      actor ≤ Subgroup.normalizer ((maximalSubgroup ⊓ target : Subgroup GroupType) :
        Set GroupType) := by
  obtain ⟨element, sylow, sylow_equal, _⟩ := signalizer_prime_local_sylow prime rank groupPrime
    prime_prime groupPrime_prime distinct actor elementary large values values_coprime
    values_invariant balanced maximalSubgroup target maximal target_compatible
  have target_preserved : conjugateSubgroup element.val⁻¹ target = target :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (common_normalizes element⁻¹.property)
  have mapped_equal := congrArg (conjugateSubgroup element.val⁻¹) sylow_equal
  change conjugateSubgroup element.val⁻¹ ((sylow : Subgroup target).map target.subtype) =
    (conjugateSubgroup element.val maximalSubgroup ⊓ target).map
      (MulAut.conj element.val⁻¹).toMonoidHom at mapped_equal
  rw [Subgroup.map_inf _ _ _ (MulAut.conj element.val⁻¹).injective] at mapped_equal
  change conjugateSubgroup element.val⁻¹ ((sylow : Subgroup target).map target.subtype) =
    conjugateSubgroup element.val⁻¹ (conjugateSubgroup element.val maximalSubgroup) ⊓
      conjugateSubgroup element.val⁻¹ target at mapped_equal
  rw [conjugate_subgroup_inv_cancel, target_preserved] at mapped_equal
  have ambient_card : Nat.card (maximalSubgroup ⊓ target : Subgroup GroupType) =
      Nat.card (sylow : Subgroup target) := by
    rw [← mapped_equal, conjugate_subgroup_card,
      Subgroup.card_map_of_injective target.subtype_injective]
  have internal_equal : (maximalSubgroup ⊓ target).subgroupOf target =
      maximalSubgroup.subgroupOf target := by
    ext element
    exact and_iff_left element.property
  have internal_pgroup : IsPGroup groupPrime (maximalSubgroup.subgroupOf target) := by
    rw [← internal_equal]
    exact (maximal.prop.2.to_le (show maximalSubgroup ⊓ target ≤ maximalSubgroup from
      inf_le_left)).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have internal_card : Nat.card (maximalSubgroup.subgroupOf target) =
      Nat.card (sylow : Subgroup target) := by
    rw [← internal_equal, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact ambient_card
  obtain ⟨result, result_equal⟩ := pgroup_sylow_of_card_eq groupPrime groupPrime_prime
    (maximalSubgroup.subgroupOf target) internal_pgroup sylow internal_card
  refine ⟨result, ?_, normalizer_inf_of_le actor maximalSubgroup target maximal.prop.1.1
    target_compatible.1⟩
  rw [result_equal, ← internal_equal, Subgroup.map_subgroupOf_eq_of_le inf_le_right]

theorem signalizer_prime_fixed_sylow
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (values_invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (maximalSubgroup : Subgroup GroupType)
    (maximal : Maximal (signalizerPrimeCompatible prime rank groupPrime actor values)
      maximalSubgroup)
    (selected fixedActor : Subgroup GroupType)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor)
    (selected_le : selected ≤ fixedActor) (fixedActor_le : fixedActor ≤ actor) :
    let localFixed := values selected ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    ∃ sylow : Sylow groupPrime localFixed,
      (sylow : Subgroup localFixed).map localFixed.subtype =
        maximalSubgroup ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ∧
      actor ≤ Subgroup.normalizer
        ((maximalSubgroup ⊓ Subgroup.centralizer (fixedActor : Set GroupType) :
          Subgroup GroupType) : Set GroupType) := by
  let localFixed := values selected ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  have centralizer_normalized : actor ≤ Subgroup.normalizer
      (Subgroup.centralizer (fixedActor : Set GroupType) : Set GroupType) :=
    (elementary_abelian_le_centralizer prime actor fixedActor elementary fixedActor_le).trans
      Subgroup.le_normalizer
  have local_compatible : signalizerCompatible prime rank actor values localFixed :=
    signalizer_compatible_inf prime rank actor values (values selected)
      (Subgroup.centralizer (fixedActor : Set GroupType))
      (signalizer_value_compatible prime rank actor values values_invariant balanced selected_member)
      centralizer_normalized
  have common_le : signalizerCommonFixed prime rank actor values ≤ localFixed := by
    refine le_inf ?_ ?_
    · exact inf_le_right.trans ((iInf_le _ selected).trans (iInf_le _ selected_member))
    · exact inf_le_left.trans (Subgroup.centralizer_le fixedActor_le)
  obtain ⟨sylow, sylow_equal, normalized⟩ :=
    signalizer_prime_local_sylow_of_common_normalizes prime rank groupPrime prime_prime
      groupPrime_prime distinct actor elementary large values values_coprime values_invariant
      balanced maximalSubgroup localFixed maximal local_compatible
      (common_le.trans Subgroup.le_normalizer)
  have fixed_equal : maximalSubgroup ⊓ localFixed =
      maximalSubgroup ⊓ Subgroup.centralizer (fixedActor : Set GroupType) := by
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · intro element member
      refine ⟨member.1, ?_, member.2⟩
      exact maximal.prop.1.2 selected selected_member
        ⟨member.1, Subgroup.centralizer_le selected_le member.2⟩
  rw [fixed_equal] at sylow_equal normalized
  exact ⟨sylow, sylow_equal, normalized⟩

end CFSG.SignalizerFunctor.Helpers
