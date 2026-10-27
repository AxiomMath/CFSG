module

public import CFSG.LocalAnalysis.SignalizerFunctor.RankFixedGrowth

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem conjugate_subgroup_not_le (element : GroupType) (target bound : Subgroup GroupType)
    (bound_preserved : conjugateSubgroup element bound = bound)
    (not_contained : ¬ target ≤ bound) : ¬ conjugateSubgroup element target ≤ bound := by
  intro contained
  have inverse_contained := Subgroup.map_mono
    (f := (MulAut.conj element⁻¹).toMonoidHom) contained
  change conjugateSubgroup element⁻¹ (conjugateSubgroup element target) ≤
    conjugateSubgroup element⁻¹ bound at inverse_contained
  rw [conjugate_subgroup_inv_cancel, ← bound_preserved,
    conjugate_subgroup_inv_cancel] at inverse_contained
  exact not_contained inverse_contained

theorem signalizer_prime_pair_growth [Finite GroupType]
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
    (first second : Subgroup GroupType)
    (first_compatible : signalizerPrimeCompatible prime rank groupPrime actor values first)
    (second_compatible : signalizerPrimeCompatible prime rank groupPrime actor values second)
    (first_proper : first ⊓ second < first) (second_proper : first ⊓ second < second) :
    ∃ element : signalizerCommonFixed prime rank actor values,
      ∃ third : Subgroup GroupType,
        Maximal (signalizerPrimeCompatible prime rank groupPrime actor values) third ∧
        first ⊓ second < conjugateSubgroup element.val first ⊓ third ∧
        first ⊓ second < second ⊓ third := by
  classical
  let intersection := first ⊓ second
  have intersection_compatible := signalizer_compatible_inf prime rank actor values first
    second first_compatible.1 second_compatible.1.1
  obtain ⟨subgroup, subgroup_member, first_escape, second_escape⟩ :=
    elementary_pair_normalizer_fixed_growth prime rank groupPrime prime_prime groupPrime_prime
      distinct actor elementary large first second first_compatible.2 second_compatible.2
      first_compatible.1.1 second_compatible.1.1 first_proper second_proper
  let localTarget := Subgroup.normalizer (intersection : Set GroupType) ⊓ values subgroup
  have local_normalized : actor ≤ Subgroup.normalizer (localTarget : Set GroupType) :=
    normalizer_inf_of_le actor _ _
      (normalizer_normalized actor intersection intersection_compatible.1)
      (values_invariant subgroup subgroup_member)
  have local_coprime : Nat.Coprime prime (Nat.card localTarget) :=
    (values_coprime subgroup subgroup_member).of_dvd_right
      (Subgroup.card_dvd_of_le (show localTarget ≤ values subgroup from inf_le_right))
  let firstLocal := first ⊓ localTarget
  let secondLocal := second ⊓ localTarget
  have firstLocal_not_le : ¬ firstLocal ≤ intersection := by
    intro contained
    apply first_escape
    rintro element ⟨⟨first_member, normalizes⟩, centralizes⟩
    apply contained
    exact ⟨first_member, normalizes,
      first_compatible.1.2 subgroup subgroup_member ⟨first_member, centralizes⟩⟩
  have secondLocal_not_le : ¬ secondLocal ≤ intersection := by
    intro contained
    apply second_escape
    rintro element ⟨⟨second_member, normalizes⟩, centralizes⟩
    apply contained
    exact ⟨second_member, normalizes,
      second_compatible.1.2 subgroup subgroup_member ⟨second_member, centralizes⟩⟩
  obtain ⟨element, element_member, combined, combined_pgroup, combined_normalized,
    combined_local, first_contains, second_contains⟩ := normalized_prime_subgroups_fuse prime
      groupPrime prime_prime groupPrime_prime actor localTarget firstLocal secondLocal
      (elementary_abelian_isPGroup prime actor elementary) local_normalized local_coprime
      inf_le_right inf_le_right (first_compatible.2.to_le inf_le_left)
      (second_compatible.2.to_le inf_le_left)
      (normalizer_inf_of_le actor first localTarget first_compatible.1.1 local_normalized)
      (normalizer_inf_of_le actor second localTarget second_compatible.1.1 local_normalized)
  have element_common : element ∈ signalizerCommonFixed prime rank actor values :=
    signalizer_common_fixed_contains_local_fixed prime rank actor values balanced subgroup_member
      ⟨element_member.1.2, element_member.2⟩
  have intersection_preserved : conjugateSubgroup element intersection = intersection :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp element_member.1.1
  have combined_compatible : signalizerCompatible prime rank actor values combined :=
    signalizer_compatible_of_le prime rank actor values
      (signalizer_value_compatible prime rank actor values values_invariant balanced subgroup_member)
      (combined_local.trans inf_le_right) combined_normalized
  have product_compatible : signalizerPrimeCompatible prime rank groupPrime actor values
      (intersection ⊔ combined) := by
    refine ⟨signalizer_sup_of_normalizing prime rank prime_prime actor elementary values
      intersection combined intersection_compatible.1 combined_normalized
      (combined_local.trans inf_le_left)
      (prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct
        combined_pgroup) intersection_compatible.2 combined_compatible.2, ?_⟩
    exact (first_compatible.2.to_le inf_le_left).to_sup_of_normal_left' combined_pgroup
      (combined_local.trans inf_le_left)
  obtain ⟨third, product_contains, third_maximal⟩ :=
    Finite.exists_le_maximal (p := signalizerPrimeCompatible prime rank groupPrime actor values)
      product_compatible
  have intersection_third : intersection ≤ third := le_sup_left.trans product_contains
  have combined_third : combined ≤ third := le_sup_right.trans product_contains
  refine ⟨⟨element, element_common⟩, third, third_maximal, ?_, ?_⟩
  · apply lt_iff_le_not_ge.mpr
    refine ⟨le_inf ?_ intersection_third, ?_⟩
    · have mapped_contains := Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom)
        (show intersection ≤ first from inf_le_left)
      change conjugateSubgroup element intersection ≤ conjugateSubgroup element first
        at mapped_contains
      rwa [intersection_preserved] at mapped_contains
    · intro no_growth
      apply conjugate_subgroup_not_le element firstLocal intersection intersection_preserved
        firstLocal_not_le
      apply le_trans _ no_growth
      exact le_inf (Subgroup.map_mono (show firstLocal ≤ first from inf_le_left))
        (first_contains.trans combined_third)
  · apply lt_iff_le_not_ge.mpr
    refine ⟨le_inf inf_le_right intersection_third, ?_⟩
    intro no_growth
    exact secondLocal_not_le ((le_inf inf_le_left (second_contains.trans combined_third)).trans
      no_growth)

end CFSG.SignalizerFunctor.Helpers
