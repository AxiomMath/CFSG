module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem completion_properties_of_centralizer_bounds (prime rank : ℕ)
    (prime_prime : prime.Prime) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    (values_coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (bounds : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) :
    let completion := ⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup
    (Nat.Coprime prime (Nat.card completion) ∧
      actor ≤ Subgroup.normalizer (completion : Set GroupType)) ∧
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      completion ⊓ Subgroup.centralizer (subgroup : Set GroupType) = values subgroup) ∧
    (∀ target : Subgroup GroupType,
      actor ≤ Subgroup.normalizer (target : Set GroupType) →
      (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
        target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) →
      target ≤ completion) := by
  let completion := ⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup
  have normalized := signalizer_completion_normalized prime rank actor values invariant
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    calc
      prime ^ rank = prime ^ rank * 1 := (mul_one _).symm
      _ ≤ prime ^ rank * prime := Nat.mul_le_mul_left _ prime_prime.one_le
  have coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values values_coprime completion normalized bounds
  refine ⟨⟨coprime, normalized⟩, ?_, ?_⟩
  · intro subgroup member
    exact le_antisymm (bounds subgroup member)
      (signalizer_value_le_completion_centralizer prime rank actor values central member)
  · intro target target_normalized target_bounds
    exact signalizer_maximality prime rank prime_prime actor elementary large values
      values_coprime target target_normalized target_bounds

omit [Finite GroupType] in
theorem centralizer_bounds_iff_exists_signalizer_upper_bound (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType) :
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) ↔
    ∃ upper : Subgroup GroupType,
      (∀ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup ≤ upper) ∧
      (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
        upper ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) := by
  constructor
  · intro bounds
    exact ⟨⨆ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup,
      fun _ member => signalizer_value_le_completion prime rank actor values member, bounds⟩
  · rintro ⟨upper, contains_values, bounds⟩
    have completion_le : (⨆ subgroup ∈ signalizerFunctorEk prime rank actor,
        values subgroup) ≤ upper := by
      apply iSup_le
      intro subgroup
      apply iSup_le
      exact contains_values subgroup
    intro subgroup member
    exact (inf_le_inf_right _ completion_le).trans (bounds subgroup member)

end CFSG.SignalizerFunctor.Helpers
