module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageLifting

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

theorem signalizer_image_completion_compatible_iff
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (kernel_compatible : signalizerCompatible prime rank actor values homomorphism.ker) :
    signalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ↔
    signalizerCompatible prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values)
      (⨆ selected ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
        signalizerImageValues homomorphism actor values selected) := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have kernel_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values coprime homomorphism.ker kernel_compatible.1 kernel_compatible.2
  have injective := actor_image_injective_of_coprime_kernel prime prime_prime homomorphism actor
    (elementary_abelian_isPGroup prime actor elementary) kernel_coprime
  have kernel_contained := signalizer_maximality prime rank prime_prime actor elementary large
    values coprime homomorphism.ker kernel_compatible.1 kernel_compatible.2
  rw [signalizer_image_completion prime rank homomorphism actor injective values]
  exact signalizer_compatible_image_iff prime rank prime_prime homomorphism actor _ elementary
    large values coprime normalized kernel_compatible kernel_contained

theorem signalizer_image_completion_bounds_iff
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (kernel_compatible : signalizerCompatible prime rank actor values homomorphism.ker) :
    (∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup) ↔
    (∀ subgroup ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      (⨆ selected ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
        signalizerImageValues homomorphism actor values selected) ⊓
          Subgroup.centralizer (subgroup : Set ImageType) ≤
            signalizerImageValues homomorphism actor values subgroup) := by
  have equivalence := signalizer_image_completion_compatible_iff prime rank prime_prime
    homomorphism actor elementary large values coprime normalized kernel_compatible
  have upstairs_normalized := signalizer_completion_normalized prime rank actor values normalized
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have kernel_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values coprime homomorphism.ker kernel_compatible.1 kernel_compatible.2
  have injective := actor_image_injective_of_coprime_kernel prime prime_prime homomorphism actor
    (elementary_abelian_isPGroup prime actor elementary) kernel_coprime
  have downstairs_normalized :=
    normalizer_image_le homomorphism actor _ upstairs_normalized
  rw [← signalizer_image_completion prime rank homomorphism actor injective values]
    at downstairs_normalized
  exact ⟨fun bounds => (equivalence.mp ⟨upstairs_normalized, bounds⟩).2,
    fun bounds => (equivalence.mpr ⟨downstairs_normalized, bounds⟩).2⟩

theorem signalizer_image_completion_comap
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (kernel_compatible : signalizerCompatible prime rank actor values homomorphism.ker) :
    (⨆ selected ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      signalizerImageValues homomorphism actor values selected).comap homomorphism =
      ⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have kernel_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values coprime homomorphism.ker kernel_compatible.1 kernel_compatible.2
  have injective := actor_image_injective_of_coprime_kernel prime prime_prime homomorphism actor
    (elementary_abelian_isPGroup prime actor elementary) kernel_coprime
  rw [signalizer_image_completion prime rank homomorphism actor injective values]
  exact Subgroup.comap_map_eq_self (signalizer_maximality prime rank prime_prime actor elementary
    large values coprime homomorphism.ker kernel_compatible.1 kernel_compatible.2)

end CFSG.SignalizerFunctor.Helpers
