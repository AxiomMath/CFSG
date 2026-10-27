module

public import CFSG.LocalAnalysis.SignalizerFunctor.SemidirectHall
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem solvable_actor_invariant_hall_containing
    (ActorType : Type actorUniverse) [Group ActorType] [Finite ActorType] [Group.IsSolvable ActorType]
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] [Group.IsSolvable GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime (Nat.card ActorType) (Nat.card GroupType))
    (primes : Set ℕ) (subgroup : Subgroup GroupType) (supported : primeSupported primes (Nat.card subgroup))
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) :
    ∃ hall : Subgroup GroupType, subgroup ≤ hall ∧ IsHallSubgroup primes hall ∧
      ∀ actorElement : ActorType, ∀ element ∈ hall, actorElement • element ∈ hall := by
  classical
  let action := MulDistribMulAction.toMulAut ActorType GroupType
  let semidirect := GroupType ⋊[action] ActorType
  let : Finite semidirect := Finite.of_equiv (GroupType × ActorType) SemidirectProduct.equivProd.symm
  let _solvable : Group.IsSolvable semidirect := solvable_semidirect_product ActorType GroupType action
  let actorPrimes : Set ℕ := {divisor | divisor.Prime ∧ divisor ∣ Nat.card ActorType}
  let enlargedPrimes := primes ∪ actorPrimes
  let embedded := invariantSemidirectSubgroup ActorType GroupType subgroup invariant
  have embedded_supported : primeSupported enlargedPrimes (Nat.card embedded) := by
    rw [invariant_semidirect_subgroup_card]
    apply prime_supported_mul
    · intro divisor divisor_prime divides
      exact Or.inl (supported divisor divisor_prime divides)
    · intro divisor divisor_prime divides
      exact Or.inr ⟨divisor_prime, divides⟩
  obtain ⟨overgroup, contains, overgroup_hall⟩ := solvable_hall_subgroup_containing semidirect
    enlargedPrimes embedded embedded_supported
  have contains_actor : ∀ actorElement : ActorType, SemidirectProduct.inr actorElement ∈ overgroup :=
    fun _ => contains subgroup.one_mem
  let hall := overgroup.comap (SemidirectProduct.inl (φ := action))
  have hall_contains : subgroup ≤ hall := fun _ member => contains member
  have hall_supported : primeSupported primes (Nat.card hall) := by
    intro divisor divisor_prime divides
    have overgroup_divides := divides.trans
      (Subgroup.card_comap_dvd_of_injective overgroup SemidirectProduct.inl SemidirectProduct.inl_injective)
    rcases overgroup_hall.1 divisor divisor_prime overgroup_divides with member | actor_member
    · exact member
    · have group_divides := divides.trans (Subgroup.card_subgroup_dvd_card hall)
      have prime_coprime := (coprime.of_dvd_left actor_member.2).of_dvd_right group_divides
      have divisor_one : divisor = 1 := by
        simpa only [Nat.Coprime, Nat.gcd_self] using prime_coprime
      exact (divisor_prime.ne_one divisor_one).elim
  have index_equal : hall.index = overgroup.index := by
    have overgroup_card := semidirect_subgroup_card_of_inr_le ActorType GroupType action overgroup contains_actor
    have overgroup_product := overgroup.card_mul_index
    have hall_product := hall.card_mul_index
    change Nat.card overgroup = Nat.card hall * Nat.card ActorType at overgroup_card
    rw [overgroup_card, SemidirectProduct.card] at overgroup_product
    nlinarith [Nat.card_pos (α := ActorType), Nat.card_pos (α := hall)]
  have index_supported : primeSupported primesᶜ hall.index := by
    rw [index_equal]
    intro divisor divisor_prime divides member
    exact overgroup_hall.2 divisor divisor_prime divides (Or.inl member)
  refine ⟨hall, hall_contains, ⟨hall_supported, index_supported⟩, ?_⟩
  intro actorElement element member
  change SemidirectProduct.inl (actorElement • element) ∈ overgroup
  rw [show actorElement • element = action actorElement element from rfl, SemidirectProduct.inl_aut]
  exact overgroup.mul_mem (overgroup.mul_mem (contains_actor actorElement) member) (contains_actor actorElement⁻¹)

theorem solvable_actor_invariant_sylow_containing
    (ActorType : Type actorUniverse) [Group ActorType] [Finite ActorType] [Group.IsSolvable ActorType]
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType] [Group.IsSolvable GroupType]
    [MulDistribMulAction ActorType GroupType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (coprime : Nat.Coprime (Nat.card ActorType) (Nat.card GroupType))
    (subgroup : Subgroup GroupType) (pgroup : IsPGroup prime subgroup)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) :
    ∃ sylow : Sylow prime GroupType, subgroup ≤ (sylow : Subgroup GroupType) ∧
      ∀ actorElement : ActorType, ∀ element ∈ (sylow : Subgroup GroupType),
        actorElement • element ∈ (sylow : Subgroup GroupType) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have supported := (prime_supported_singleton_iff_pgroup prime prime_prime subgroup).mpr pgroup
  obtain ⟨hall, contains, hall_property, hall_invariant⟩ := solvable_actor_invariant_hall_containing ActorType
    GroupType coprime {prime} subgroup supported invariant
  have hall_pgroup := (prime_supported_singleton_iff_pgroup prime prime_prime hall).mp hall_property.1
  have index_prime : ¬ prime ∣ hall.index := by
    intro divides
    exact hall_property.2 prime prime_prime divides rfl
  exact ⟨hall_pgroup.toSylow index_prime, by rwa [IsPGroup.toSylow_coe], by rwa [IsPGroup.toSylow_coe]⟩

end CFSG.SignalizerFunctor.Helpers
