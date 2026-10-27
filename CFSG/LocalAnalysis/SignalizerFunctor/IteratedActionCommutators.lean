module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageAmbientNormalizers
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionCommutators

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType]

@[expose] def invariantActionCommutator (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    Subgroup GroupType :=
  let _action := invariantSubgroupAction parent invariant
  (actionCommutator (ActorType := ActorType) (GroupType := parent)).map parent.subtype

theorem invariant_action_commutator_le (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    invariantActionCommutator parent invariant ≤ parent := Subgroup.map_subtype_le _

theorem invariant_action_commutator_generator (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (actorElement : ActorType) (element : GroupType) (member : element ∈ parent) :
    element⁻¹ * (actorElement • element) ∈ invariantActionCommutator parent invariant := by
  let _action := invariantSubgroupAction parent invariant
  exact Subgroup.mem_map_of_mem parent.subtype
    (action_commutator_generator actorElement (⟨element, member⟩ : parent))

theorem invariant_action_commutator_normalized (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    parent ≤ Subgroup.normalizer (invariantActionCommutator parent invariant : Set GroupType) := by
  let _action := invariantSubgroupAction parent invariant
  let internal := actionCommutator (ActorType := ActorType) (GroupType := parent)
  let _normal : internal.Normal := action_commutator_normal
  have formula := normalizer_subtype_map parent internal
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at formula
  exact formula.le.trans inf_le_right

theorem invariant_action_commutator_invariant (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    ∀ actorElement : ActorType, ∀ element ∈ invariantActionCommutator parent invariant,
      actorElement • element ∈ invariantActionCommutator parent invariant := by
  let _action := invariantSubgroupAction parent invariant
  rintro actorElement _ ⟨element, member, rfl⟩
  exact Subgroup.mem_map_of_mem parent.subtype (action_commutator_invariant actorElement element member)

theorem fixed_normalizes_invariant_action_commutator (parent : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent)
    (normalized : FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (parent : Set GroupType)) :
    FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (invariantActionCommutator parent invariant : Set GroupType) := by
  let _action := invariantSubgroupAction parent invariant
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator fixed element member
  let commutators := invariantActionCommutator parent invariant
  have map_le : commutators.map (MulAut.conj conjugator).toMonoidHom ≤ commutators := by
    change ((actionCommutator (ActorType := ActorType) (GroupType := parent)).map parent.subtype).map
      (MulAut.conj conjugator).toMonoidHom ≤ commutators
    rw [Subgroup.map_map]
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, original, rfl⟩
    change conjugator * (original.val⁻¹ * (actorElement • original.val)) * conjugator⁻¹ ∈ commutators
    have conjugated_member := Subgroup.le_normalizer_iff.mp normalized conjugator fixed original.val original.property
    have generated := invariant_action_commutator_generator parent invariant actorElement
      (conjugator * original.val * conjugator⁻¹) conjugated_member
    have equal : (conjugator * original.val * conjugator⁻¹)⁻¹ *
        (actorElement • (conjugator * original.val * conjugator⁻¹)) =
        conjugator * (original.val⁻¹ * (actorElement • original.val)) * conjugator⁻¹ := by
      rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, fixed actorElement,
        smul_inv', fixed actorElement]
      group
    rwa [equal] at generated
  exact map_le (Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom member)

theorem coprime_iterated_action_commutator_normal [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    (invariantActionCommutator (actionCommutator (ActorType := ActorType) (GroupType := GroupType))
      action_commutator_invariant).Normal := by
  let commutators := actionCommutator (ActorType := ActorType) (GroupType := GroupType)
  let _normal := action_commutator_normal (ActorType := ActorType) (GroupType := GroupType)
  let iterated := invariantActionCommutator commutators action_commutator_invariant
  have normalized : (⊤ : Subgroup GroupType) ≤ Subgroup.normalizer (iterated : Set GroupType) := by
    rw [← coprime_action_commutator_factorization prime prime_prime actor_pgroup coprime]
    exact sup_le (invariant_action_commutator_normalized commutators action_commutator_invariant)
      (fixed_normalizes_invariant_action_commutator commutators action_commutator_invariant
        Subgroup.le_normalizer_of_normal)
  exact Subgroup.normalizer_eq_top_iff.mp (top_unique normalized)

theorem coprime_action_commutator_idempotent [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) :
    invariantActionCommutator (actionCommutator (ActorType := ActorType) (GroupType := GroupType))
      action_commutator_invariant = actionCommutator (ActorType := ActorType) (GroupType := GroupType) := by
  let commutators := actionCommutator (ActorType := ActorType) (GroupType := GroupType)
  let iterated := invariantActionCommutator commutators action_commutator_invariant
  let _normal : iterated.Normal := coprime_iterated_action_commutator_normal prime prime_prime actor_pgroup coprime
  have iterated_invariant := invariant_action_commutator_invariant commutators action_commutator_invariant
  let _quotientAction := invariantQuotientAction iterated iterated_invariant
  let projection := QuotientGroup.mk' iterated
  have commutators_fixed : ∀ actorElement : ActorType, ∀ element ∈ commutators,
      projection (actorElement • element) = projection element := by
    intro actorElement element member
    have difference_one : projection (element⁻¹ * (actorElement • element)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (invariant_action_commutator_generator commutators
        action_commutator_invariant actorElement element member)
    rw [map_mul, map_inv, inv_mul_eq_one] at difference_one
    exact difference_one.symm
  have generator_le : commutators ≤ iterated := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, element, rfl⟩
    let difference := projection (element⁻¹ * (actorElement • element))
    have difference_fixed : actorElement • difference = difference := by
      exact commutators_fixed actorElement _ (action_commutator_generator actorElement element)
    have iterate : ∀ exponent : ℕ,
        actorElement ^ exponent • projection element = projection element * difference ^ exponent := by
      intro exponent
      induction exponent with
      | zero => simp only [pow_zero, one_smul, mul_one]
      | succ exponent induction_hypothesis =>
        rw [pow_succ', mul_smul, induction_hypothesis, MulDistribMulAction.smul_mul, smul_pow', difference_fixed]
        have first_step : actorElement • projection element = projection element * difference := by
          change projection (actorElement • element) = projection element *
            projection (element⁻¹ * (actorElement • element))
          rw [map_mul, map_inv, ← mul_assoc, mul_inv_cancel, one_mul]
        rw [first_step, mul_assoc, ← pow_succ']
    have difference_power : difference ^ orderOf actorElement = 1 := by
      have identity := iterate (orderOf actorElement)
      rw [pow_orderOf_eq_one, one_smul] at identity
      exact (mul_left_cancel (identity.symm.trans (mul_one _).symm))
    have orders_coprime : Nat.Coprime (orderOf actorElement) (Nat.card (GroupType ⧸ iterated)) :=
      (actor_pgroup.orderOf_coprime coprime actorElement).of_dvd_right
        (Subgroup.card_quotient_dvd_card iterated)
    have difference_one : difference = 1 :=
      (pow_eq_one_iff_of_coprime orders_coprime).mp ⟨difference_power, pow_card_eq_one'⟩
    exact (QuotientGroup.eq_one_iff _).mp difference_one
  exact le_antisymm (invariant_action_commutator_le commutators action_commutator_invariant) generator_le

end CFSG.SignalizerFunctor.Helpers
