module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleSubgroups

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

abbrev conjugateSubgroup (element : GroupType) (target : Subgroup GroupType) :
    Subgroup GroupType := target.map (MulAut.conj element).toMonoidHom

theorem conjugate_subgroup_one (target : Subgroup GroupType) :
    conjugateSubgroup 1 target = target := by
  change target.map (MulAut.conj 1).toMonoidHom = target
  have identity : (MulAut.conj (1 : GroupType)).toMonoidHom = MonoidHom.id GroupType := by
    ext element
    simp
  rw [identity, Subgroup.map_id]

theorem conjugate_subgroup_mul (first second : GroupType) (target : Subgroup GroupType) :
    conjugateSubgroup first (conjugateSubgroup second target) =
      conjugateSubgroup (first * second) target := by
  change (target.map (MulAut.conj second).toMonoidHom).map
    (MulAut.conj first).toMonoidHom = target.map (MulAut.conj (first * second)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext element
  change first * (second * element * second⁻¹) * first⁻¹ =
    (first * second) * element * (first * second)⁻¹
  group

theorem conjugate_subgroup_inv_cancel (element : GroupType) (target : Subgroup GroupType) :
    conjugateSubgroup element⁻¹ (conjugateSubgroup element target) = target := by
  rw [conjugate_subgroup_mul, inv_mul_cancel, conjugate_subgroup_one]

theorem conjugate_subgroup_card (element : GroupType) (target : Subgroup GroupType) :
    Nat.card (conjugateSubgroup element target) = Nat.card target :=
  Subgroup.card_map_of_injective (MulAut.conj element).injective

@[expose] def signalizerPrimeCompatible (prime rank groupPrime : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType) : Prop :=
  signalizerCompatible prime rank actor values target ∧ IsPGroup groupPrime target

theorem signalizer_prime_compatible_conjugate (prime rank groupPrime : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (target : Subgroup GroupType)
    (compatible : signalizerPrimeCompatible prime rank groupPrime actor values target)
    (element : signalizerCommonFixed prime rank actor values) :
    signalizerPrimeCompatible prime rank groupPrime actor values
      (conjugateSubgroup element.val target) := by
  exact ⟨signalizer_compatible_conjugate prime rank actor values target compatible.1 element,
    compatible.2.of_equiv ((MulAut.conj element.val).subgroupMap target)⟩

theorem signalizer_prime_maximal_conjugate (prime rank groupPrime : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (target : Subgroup GroupType)
    (maximal : Maximal (signalizerPrimeCompatible prime rank groupPrime actor values) target)
    (element : signalizerCommonFixed prime rank actor values) :
    Maximal (signalizerPrimeCompatible prime rank groupPrime actor values)
      (conjugateSubgroup element.val target) := by
  apply maximal_iff.mpr
  refine ⟨signalizer_prime_compatible_conjugate prime rank groupPrime actor values target
    maximal.prop element, ?_⟩
  intro other compatible contains
  have inverse_compatible := signalizer_prime_compatible_conjugate prime rank groupPrime
    actor values other compatible element⁻¹
  have original_contains := Subgroup.map_mono (f := (MulAut.conj element.val⁻¹).toMonoidHom)
    contains
  change conjugateSubgroup element.val⁻¹ (conjugateSubgroup element.val target) ≤
    conjugateSubgroup element.val⁻¹ other at original_contains
  rw [conjugate_subgroup_inv_cancel] at original_contains
  have equality := (maximal_iff.mp maximal).2 inverse_compatible original_contains
  have mapped_equality := congrArg (conjugateSubgroup element.val) equality
  change conjugateSubgroup element.val target =
    conjugateSubgroup element.val (conjugateSubgroup element.val⁻¹ other) at mapped_equality
  rw [conjugate_subgroup_mul, mul_inv_cancel, conjugate_subgroup_one] at mapped_equality
  exact mapped_equality

@[expose] def signalizerConjugate (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (first second : Subgroup GroupType) : Prop :=
  ∃ element : signalizerCommonFixed prime rank actor values,
    conjugateSubgroup element.val first = second

theorem signalizer_conjugate_refl (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType) :
    signalizerConjugate prime rank actor values target target :=
  ⟨1, conjugate_subgroup_one target⟩

theorem signalizer_conjugate_symm (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) {first second : Subgroup GroupType}
    (conjugate : signalizerConjugate prime rank actor values first second) :
    signalizerConjugate prime rank actor values second first := by
  obtain ⟨element, equality⟩ := conjugate
  refine ⟨element⁻¹, ?_⟩
  change conjugateSubgroup element.val⁻¹ second = first
  rw [← equality, conjugate_subgroup_inv_cancel]

theorem signalizer_conjugate_trans (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) {first middle last : Subgroup GroupType}
    (first_conjugate : signalizerConjugate prime rank actor values first middle)
    (second_conjugate : signalizerConjugate prime rank actor values middle last) :
    signalizerConjugate prime rank actor values first last := by
  obtain ⟨firstElement, first_equality⟩ := first_conjugate
  obtain ⟨secondElement, second_equality⟩ := second_conjugate
  refine ⟨secondElement * firstElement, ?_⟩
  change conjugateSubgroup (secondElement.val * firstElement.val) first = last
  rw [← conjugate_subgroup_mul, first_equality, second_equality]

theorem signalizer_common_fixed_contains_local_fixed (prime rank : ℕ)
    (actor : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    {subgroup : Subgroup GroupType} (member : subgroup ∈ signalizerFunctorEk prime rank actor) :
    values subgroup ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      signalizerCommonFixed prime rank actor values :=
  le_of_eq (signalizer_value_common_fixed prime rank actor values balanced member)

end CFSG.SignalizerFunctor.Helpers
