module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeSubfunctor
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImages
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSubgroups

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

structure SolvableSignalizerConditions (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Prop where
  central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
    values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType)
  coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
    Nat.Coprime prime (Nat.card (values subgroup))
  normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
    actor ≤ Subgroup.normalizer (values subgroup : Set GroupType)
  balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
    ∀ other ∈ signalizerFunctorEk prime rank actor,
      values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other
  solvable : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
    Group.IsSolvable (values subgroup)

theorem solvable_signalizer_image_conditions (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values) :
    SolvableSignalizerConditions prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values) := by
  have properties := signalizer_image_properties prime rank prime_prime homomorphism actor elementary
    injective values conditions.central conditions.coprime conditions.normalized conditions.balanced
  exact ⟨fun subgroup member => (properties.1 subgroup member).1,
    fun subgroup member => (properties.1 subgroup member).2.1,
    fun subgroup member => (properties.1 subgroup member).2.2, properties.2,
    signalizer_image_solvable prime rank homomorphism actor injective values conditions.solvable⟩

theorem solvable_signalizer_subgroup_conditions [Finite GroupType] (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values) :
    SolvableSignalizerConditions prime rank (actor.subgroupOf ambient)
      (signalizerSubgroupValues ambient values) := by
  have properties := signalizer_subgroup_properties prime rank actor ambient contained values
    conditions.central conditions.coprime conditions.normalized conditions.balanced
  exact ⟨fun subgroup member => (properties.1 subgroup member).1,
    fun subgroup member => (properties.1 subgroup member).2.1,
    fun subgroup member => (properties.1 subgroup member).2.2, properties.2,
    signalizer_subgroup_solvable prime rank actor ambient contained values conditions.solvable⟩

theorem solvable_signalizer_prime_subfunctor_conditions [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values) (primes : Set ℕ) :
    SolvableSignalizerConditions prime rank actor (signalizerPrimeValue prime rank actor values primes) := by
  have properties := signalizer_prime_subfunctor_properties prime rank prime_prime actor elementary
    values primes conditions.central conditions.coprime conditions.normalized conditions.balanced
    conditions.solvable
  exact ⟨fun subgroup member => (properties.1 subgroup member).1,
    fun subgroup member => (properties.1 subgroup member).2.1,
    fun subgroup member => (properties.1 subgroup member).2.2.1, properties.2,
    fun subgroup member => (properties.1 subgroup member).2.2.2.1⟩

theorem normal_quotient_card_strict [Finite GroupType]
    (normal : Subgroup GroupType) [normal.Normal] (nontrivial : normal ≠ ⊥) :
    Nat.card (GroupType ⧸ normal) < Nat.card GroupType := by
  have normal_card_positive : 0 < Nat.card normal := Nat.card_pos
  have quotient_card_positive : 0 < Nat.card (GroupType ⧸ normal) := Nat.card_pos
  have normal_card_not_one : Nat.card normal ≠ 1 := by
    intro equal
    exact nontrivial ((Subgroup.eq_bot_iff_card normal).mpr equal)
  have card_formula := normal.card_mul_index
  rw [normal.index_eq_card] at card_formula
  have normal_card_large : 1 < Nat.card normal := by omega
  calc
    Nat.card (GroupType ⧸ normal) = 1 * Nat.card (GroupType ⧸ normal) := (one_mul _).symm
    _ < Nat.card normal * Nat.card (GroupType ⧸ normal) :=
      Nat.mul_lt_mul_of_pos_right normal_card_large quotient_card_positive
    _ = Nat.card GroupType := card_formula

end CFSG.SignalizerFunctor.Helpers
