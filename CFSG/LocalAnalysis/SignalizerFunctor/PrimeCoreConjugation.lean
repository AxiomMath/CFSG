module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSetCore
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableCompatibility

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem prime_set_core_map_isomorphism {ImageType : Type imageUniverse} [Group ImageType] [Finite ImageType]
    (primes : Set ℕ) (equivalence : GroupType ≃* ImageType) :
    (primeSetCore (GroupType := GroupType) primes).map equivalence.toMonoidHom =
      primeSetCore (GroupType := ImageType) primes := by
  have map_le : ∀ {Source : Type groupUniverse} [Group Source] [Finite Source]
      {Target : Type imageUniverse} [Group Target] [Finite Target] (isomorphism : Source ≃* Target),
      (primeSetCore (GroupType := Source) primes).map isomorphism.toMonoidHom ≤
        primeSetCore (GroupType := Target) primes := by
    intro Source _ _ Target _ _ isomorphism
    apply prime_set_core_contains
    · exact (prime_set_core_normal primes).map isomorphism.toMonoidHom isomorphism.surjective
    · rw [Subgroup.card_map_of_injective isomorphism.injective]
      exact prime_set_core_supported primes
  apply le_antisymm (map_le equivalence)
  have inverse_le : (primeSetCore (GroupType := ImageType) primes).map equivalence.symm.toMonoidHom ≤
      primeSetCore (GroupType := GroupType) primes := by
    apply prime_set_core_contains
    · exact (prime_set_core_normal primes).map equivalence.symm.toMonoidHom equivalence.symm.surjective
    · rw [Subgroup.card_map_of_injective equivalence.symm.injective]
      exact prime_set_core_supported primes
  have mapped_le := Subgroup.map_mono (f := equivalence.toMonoidHom) inverse_le
  rw [Subgroup.map_map] at mapped_le
  have identity : equivalence.toMonoidHom.comp equivalence.symm.toMonoidHom = MonoidHom.id ImageType := by
    ext element
    exact equivalence.apply_symm_apply element
  rw [identity, Subgroup.map_id] at mapped_le
  exact mapped_le

theorem embedded_prime_core_conjugate (primes : Set ℕ) (element : GroupType)
    (parent : Subgroup GroupType) :
    conjugateSubgroup element ((primeSetCore (GroupType := parent) primes).map parent.subtype) =
      (primeSetCore (GroupType := conjugateSubgroup element parent) primes).map
        (conjugateSubgroup element parent).subtype := by
  let equivalence := parent.equivMapOfInjective (MulAut.conj element).toMonoidHom
    (MulAut.conj element).injective
  have core_eq := prime_set_core_map_isomorphism primes equivalence
  have mapped_eq := congrArg (Subgroup.map (conjugateSubgroup element parent).subtype) core_eq
  rw [Subgroup.map_map] at mapped_eq
  change ((primeSetCore (GroupType := parent) primes).map parent.subtype).map
    (MulAut.conj element).toMonoidHom = _
  rw [Subgroup.map_map]
  have hom_eq : (conjugateSubgroup element parent).subtype.comp equivalence.toMonoidHom =
      (MulAut.conj element).toMonoidHom.comp parent.subtype := by
    ext value
    rfl
  rwa [hom_eq] at mapped_eq

omit [Finite GroupType] in
theorem solvable_signalizer_compatible_conjugate (prime rank : ℕ) (actor parent : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (compatible : solvableSignalizerCompatible prime rank actor values parent)
    (element : signalizerCommonFixed prime rank actor values) :
    solvableSignalizerCompatible prime rank actor values (conjugateSubgroup element.val parent) := by
  let := compatible.2
  exact ⟨signalizer_compatible_conjugate prime rank actor values parent compatible.1 element,
    Group.isSolvable_of_surjective (f := ((MulAut.conj element.val).subgroupMap parent).toMonoidHom)
      ((MulAut.conj element.val).subgroupMap parent).surjective⟩

theorem signalizer_model_factorization_conjugate (prime rank groupPrime : ℕ)
    (actor source model : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (factorization : model =
      (primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype ⊔ (source ⊓ model))
    (element : signalizerCommonFixed prime rank actor values) :
    conjugateSubgroup element.val model =
      (primeSetCore (GroupType := conjugateSubgroup element.val model) ({groupPrime}ᶜ)).map
        (conjugateSubgroup element.val model).subtype ⊔
          (conjugateSubgroup element.val source ⊓ conjugateSubgroup element.val model) := by
  have mapped_eq := congrArg (Subgroup.map (MulAut.conj element.val).toMonoidHom) factorization
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj element.val).injective] at mapped_eq
  change conjugateSubgroup element.val model =
    conjugateSubgroup element.val ((primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype) ⊔
      (conjugateSubgroup element.val source ⊓ conjugateSubgroup element.val model) at mapped_eq
  rwa [embedded_prime_core_conjugate] at mapped_eq

end CFSG.SignalizerFunctor.Helpers
