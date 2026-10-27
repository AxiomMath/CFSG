module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleGrowth

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem subgroup_card_strict_mono [Finite GroupType] {smaller larger : Subgroup GroupType}
    (proper : smaller < larger) : Nat.card smaller < Nat.card larger := by
  apply lt_of_not_ge
  intro cardinality
  exact proper.ne (Subgroup.eq_of_le_of_card_ge proper.le cardinality)

theorem signalizer_prime_transitivity [Finite GroupType]
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
    (first_maximal : Maximal (signalizerPrimeCompatible prime rank groupPrime actor values) first)
    (second_maximal : Maximal (signalizerPrimeCompatible prime rank groupPrime actor values) second) :
    signalizerConjugate prime rank actor values first second := by
  classical
  by_contra nonconjugate
  let badPairs := {pair : Subgroup GroupType × Subgroup GroupType //
    Maximal (signalizerPrimeCompatible prime rank groupPrime actor values) pair.1 ∧
    Maximal (signalizerPrimeCompatible prime rank groupPrime actor values) pair.2 ∧
    ¬ signalizerConjugate prime rank actor values pair.1 pair.2}
  have : Nonempty badPairs := ⟨⟨⟨first, second⟩, first_maximal, second_maximal, nonconjugate⟩⟩
  let weight : badPairs → ℕ := fun pair =>
    Nat.card (pair.val.1 ⊓ pair.val.2 : Subgroup GroupType)
  obtain ⟨maximalPair, optimal⟩ := Finite.exists_max weight
  let left := maximalPair.val.1
  let right := maximalPair.val.2
  have left_maximal := maximalPair.property.1
  have right_maximal := maximalPair.property.2.1
  have not_conjugate := maximalPair.property.2.2
  have left_not_le : ¬ left ≤ right := by
    intro contains
    have equality := (maximal_iff.mp left_maximal).2 right_maximal.prop contains
    change left = right at equality
    apply not_conjugate
    change signalizerConjugate prime rank actor values left right
    rw [equality]
    exact signalizer_conjugate_refl prime rank actor values right
  have right_not_le : ¬ right ≤ left := by
    intro contains
    have equality := (maximal_iff.mp right_maximal).2 left_maximal.prop contains
    change right = left at equality
    apply not_conjugate
    change signalizerConjugate prime rank actor values left right
    rw [equality]
    exact signalizer_conjugate_refl prime rank actor values left
  have left_proper : left ⊓ right < left :=
    lt_iff_le_not_ge.mpr ⟨inf_le_left, fun contains => left_not_le (contains.trans inf_le_right)⟩
  have right_proper : left ⊓ right < right :=
    lt_iff_le_not_ge.mpr ⟨inf_le_right, fun contains => right_not_le (contains.trans inf_le_left)⟩
  obtain ⟨element, third, third_maximal, left_growth, right_growth⟩ :=
    signalizer_prime_pair_growth prime rank groupPrime prime_prime groupPrime_prime distinct
      actor elementary large values values_coprime values_invariant balanced left right
      left_maximal.prop right_maximal.prop left_proper right_proper
  have left_conjugate_maximal := signalizer_prime_maximal_conjugate prime rank groupPrime actor
    values left left_maximal element
  have left_third_conjugate : signalizerConjugate prime rank actor values
      (conjugateSubgroup element.val left) third := by
    by_contra still_bad
    let badPair : badPairs := ⟨⟨conjugateSubgroup element.val left, third⟩,
      left_conjugate_maximal, third_maximal, still_bad⟩
    have no_larger := optimal badPair
    change Nat.card (conjugateSubgroup element.val left ⊓ third : Subgroup GroupType) ≤
      Nat.card (left ⊓ right : Subgroup GroupType) at no_larger
    exact (subgroup_card_strict_mono left_growth).not_ge no_larger
  have right_third_conjugate : signalizerConjugate prime rank actor values right third := by
    by_contra still_bad
    let badPair : badPairs := ⟨⟨right, third⟩, right_maximal, third_maximal, still_bad⟩
    have no_larger := optimal badPair
    change Nat.card (right ⊓ third : Subgroup GroupType) ≤
      Nat.card (left ⊓ right : Subgroup GroupType) at no_larger
    exact (subgroup_card_strict_mono right_growth).not_ge no_larger
  have left_third := signalizer_conjugate_trans prime rank actor values
    (show signalizerConjugate prime rank actor values left
      (conjugateSubgroup element.val left) from ⟨element, rfl⟩) left_third_conjugate
  exact not_conjugate (signalizer_conjugate_trans prime rank actor values left_third
    (signalizer_conjugate_symm prime rank actor values right_third_conjugate))

end CFSG.SignalizerFunctor.Helpers
