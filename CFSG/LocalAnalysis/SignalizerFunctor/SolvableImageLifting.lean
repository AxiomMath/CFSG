module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageLifting
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableCompatibility

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

theorem subgroup_solvable_iff_image_of_solvable_kernel
    (homomorphism : GroupType →* ImageType) (target : Subgroup GroupType)
    (kernel_solvable : Group.IsSolvable homomorphism.ker)
    (contains_kernel : homomorphism.ker ≤ target) :
    Group.IsSolvable target ↔ Group.IsSolvable (target.map homomorphism) := by
  constructor
  · intro solvable
    let := solvable
    exact Group.isSolvable_of_surjective (subgroup_image_hom_surjective homomorphism target)
  · intro image_solvable
    let := image_solvable
    let := kernel_solvable
    let inclusion := Subgroup.inclusion contains_kernel
    let restricted := subgroupImageHom homomorphism target
    apply Group.isSolvable_of_ker_le_range inclusion restricted
    intro element member
    have ambient_member : element.val ∈ homomorphism.ker := by
      exact congrArg (fun imageElement : target.map homomorphism => imageElement.val) member
    exact ⟨⟨element.val, ambient_member⟩, rfl⟩

theorem solvable_signalizer_compatible_image_iff [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (normalized : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (kernel_compatible : solvableSignalizerCompatible prime rank actor values homomorphism.ker)
    (contains_kernel : homomorphism.ker ≤ target) :
    solvableSignalizerCompatible prime rank actor values target ↔
      solvableSignalizerCompatible prime rank (actor.map homomorphism)
        (signalizerImageValues homomorphism actor values) (target.map homomorphism) := by
  exact and_congr
    (signalizer_compatible_image_iff prime rank prime_prime homomorphism actor target elementary
      large values coprime normalized kernel_compatible.1 contains_kernel)
    (subgroup_solvable_iff_image_of_solvable_kernel homomorphism target kernel_compatible.2 contains_kernel)

theorem solvable_signalizer_image_completion_iff [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values selected)))
    (normalized : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values selected : Set GroupType))
    (kernel_compatible : solvableSignalizerCompatible prime rank actor values homomorphism.ker) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ↔
    solvableSignalizerCompatible prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values)
      (⨆ selected ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
        signalizerImageValues homomorphism actor values selected) := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have kernel_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values coprime homomorphism.ker kernel_compatible.1.1 kernel_compatible.1.2
  have actor_injective := actor_image_injective_of_coprime_kernel prime prime_prime homomorphism actor
    (elementary_abelian_isPGroup prime actor elementary) kernel_coprime
  have kernel_contained := signalizer_maximality prime rank prime_prime actor elementary large values
    coprime homomorphism.ker kernel_compatible.1.1 kernel_compatible.1.2
  rw [signalizer_image_completion prime rank homomorphism actor actor_injective values]
  exact solvable_signalizer_compatible_image_iff prime rank prime_prime homomorphism actor _ elementary
    large values coprime normalized kernel_compatible kernel_contained

end CFSG.SignalizerFunctor.Helpers
