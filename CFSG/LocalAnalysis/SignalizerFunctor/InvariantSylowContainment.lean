module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantActions

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType]

theorem normalizer_invariant_of_invariant (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    ∀ actorElement : ActorType, ∀ element ∈ Subgroup.normalizer (subgroup : Set GroupType),
      actorElement • element ∈ Subgroup.normalizer (subgroup : Set GroupType) := by
  intro actorElement element member
  have image : subgroup.map
      (MulDistribMulAction.toMulEquiv GroupType actorElement).toMonoidHom = subgroup := by
    apply le_antisymm
    · rintro value ⟨representative, representative_member, rfl⟩
      exact invariant actorElement representative representative_member
    · intro value value_member
      refine ⟨actorElement⁻¹ • value, invariant actorElement⁻¹ value value_member, ?_⟩
      exact smul_inv_smul actorElement value
  have mapped_member := Subgroup.mem_map_of_mem
    (MulDistribMulAction.toMulEquiv GroupType actorElement).toMonoidHom member
  rw [Subgroup.map_equiv_normalizer_eq, image] at mapped_member
  exact mapped_member

theorem invariant_sylow_containing [Finite GroupType]
    (prime sylowPrime : ℕ) (prime_prime : prime.Prime)
    (sylowPrime_prime : sylowPrime.Prime)
    (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (subgroup : Subgroup GroupType) (subgroup_pgroup : IsPGroup sylowPrime subgroup)
    (subgroup_invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    ∃ sylow : Sylow sylowPrime GroupType, subgroup ≤ sylow ∧
      ∀ actorElement : ActorType, actorElement • sylow = sylow := by
  classical
  let : Fact sylowPrime.Prime := ⟨sylowPrime_prime⟩
  let property : Subgroup GroupType → Prop := fun candidate =>
    IsPGroup sylowPrime candidate ∧ ∀ actorElement : ActorType, ∀ element ∈ candidate,
      actorElement • element ∈ candidate
  obtain ⟨maximalSubgroup, contains, maximal⟩ :=
    Finite.exists_le_maximal (p := property) ⟨subgroup_pgroup, subgroup_invariant⟩
  have maximal_pgroup := maximal.prop.1
  have maximal_invariant := maximal.prop.2
  let normalizer := Subgroup.normalizer (maximalSubgroup : Set GroupType)
  have normalizer_invariant := normalizer_invariant_of_invariant maximalSubgroup maximal_invariant
  let _normalizerAction := invariantSubgroupAction normalizer normalizer_invariant
  have normalizer_coprime : Nat.Coprime prime (Nat.card normalizer) :=
    coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card normalizer)
  obtain ⟨normalizerSylow, normalizerSylow_fixed⟩ := invariant_sylow_exists prime sylowPrime
    prime_prime sylowPrime_prime actor_pgroup normalizer_coprime
  let embedded : Subgroup GroupType :=
    (normalizerSylow : Subgroup normalizer).map normalizer.subtype
  have embedded_pgroup : IsPGroup sylowPrime embedded :=
    normalizerSylow.isPGroup'.map normalizer.subtype
  have embedded_invariant : ∀ actorElement : ActorType, ∀ element ∈ embedded,
      actorElement • element ∈ embedded := by
    intro actorElement element member
    obtain ⟨representative, representative_member, rfl⟩ := member
    have preserved : actorElement • representative ∈ (normalizerSylow : Subgroup normalizer) := by
      have image_member := Subgroup.smul_mem_pointwise_smul representative actorElement
        (normalizerSylow : Subgroup normalizer) representative_member
      rw [← Sylow.pointwise_smul_def, normalizerSylow_fixed] at image_member
      exact image_member
    exact Subgroup.mem_map_of_mem normalizer.subtype preserved
  have maximal_le_normalizer : maximalSubgroup ≤ normalizer := Subgroup.le_normalizer
  let internal := maximalSubgroup.subgroupOf normalizer
  let _normal : internal.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (show normalizer ≤ normalizer from le_rfl)
  have internal_pgroup : IsPGroup sylowPrime internal :=
    maximal_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe maximal_le_normalizer).symm
  have internal_le : internal ≤ (normalizerSylow : Subgroup normalizer) :=
    internal_pgroup.le_sylow_of_normal normalizerSylow
  have maximal_le_embedded : maximalSubgroup ≤ embedded := by
    rw [← Subgroup.map_subgroupOf_eq_of_le maximal_le_normalizer]
    exact Subgroup.map_mono internal_le
  have embedded_eq : embedded = maximalSubgroup :=
    le_antisymm (maximal.le_of_ge ⟨embedded_pgroup, embedded_invariant⟩ maximal_le_embedded)
      maximal_le_embedded
  have index_prime : ¬ sylowPrime ∣ maximalSubgroup.index := by
    intro divides_index
    obtain ⟨exponent, cardinality⟩ := maximal_pgroup.exists_card_eq
    have higher_divides : sylowPrime ^ (exponent + 1) ∣ Nat.card GroupType := by
      rw [← maximalSubgroup.card_mul_index, cardinality, pow_succ]
      exact Nat.mul_dvd_mul_left _ divides_index
    have normalizer_divides : sylowPrime ^ (exponent + 1) ∣ Nat.card normalizer :=
      Sylow.prime_pow_dvd_card_normalizer higher_divides cardinality
    have sylow_divides := normalizerSylow.pow_dvd_card_of_pow_dvd_card normalizer_divides
    have embedded_card : Nat.card embedded = Nat.card (normalizerSylow : Subgroup normalizer) :=
      Subgroup.card_map_of_injective normalizer.subtype_injective
    rw [← embedded_card, embedded_eq, cardinality] at sylow_divides
    have impossible_bound := Nat.le_of_dvd (pow_pos sylowPrime_prime.pos exponent) sylow_divides
    have power_increases : sylowPrime ^ exponent < sylowPrime ^ (exponent + 1) := by
      rw [pow_succ]
      exact lt_mul_of_one_lt_right (pow_pos sylowPrime_prime.pos exponent) sylowPrime_prime.one_lt
    exact (not_le_of_gt power_increases) impossible_bound
  let sylow := maximal_pgroup.toSylow index_prime
  refine ⟨sylow, ?_, ?_⟩
  · simpa only [sylow, IsPGroup.toSylow_coe] using contains
  · intro actorElement
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, IsPGroup.toSylow_coe]
    apply le_antisymm
    · rintro element ⟨representative, representative_member, rfl⟩
      exact maximal_invariant actorElement representative representative_member
    · intro element member
      refine ⟨actorElement⁻¹ • element, maximal_invariant actorElement⁻¹ element member, ?_⟩
      exact smul_inv_smul actorElement element

end CFSG.SignalizerFunctor.Helpers
