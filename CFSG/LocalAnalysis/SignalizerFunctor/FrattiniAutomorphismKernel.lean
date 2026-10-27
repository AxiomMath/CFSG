module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def frattiniAutomorphismKernel (GroupType : Type groupUniverse) [Group GroupType] :
    Subgroup (MulAut GroupType) where
  carrier := {automorphism | ∀ element : GroupType,
    QuotientGroup.mk' (frattini GroupType) (automorphism element) =
      QuotientGroup.mk' (frattini GroupType) element}
  one_mem' := by intro element; rfl
  mul_mem' := by
    intro first second first_member second_member element
    change QuotientGroup.mk' (frattini GroupType) (first (second element)) = _
    rw [first_member, second_member]
  inv_mem' := by
    intro automorphism member element
    have equal := member (automorphism⁻¹ element)
    rw [MulAut.apply_inv_self] at equal
    exact equal.symm

omit [Finite GroupType] in
theorem frattini_automorphism_kernel_normal : (frattiniAutomorphismKernel GroupType).Normal := by
  constructor
  intro automorphism member conjugator element
  have invariant : ∀ actorElement : MulAut GroupType, ∀ value ∈ frattini GroupType,
      actorElement • value ∈ frattini GroupType := by
    intro actorElement value value_member
    exact Subgroup.characteristic_iff_le_comap.mp inferInstance actorElement value_member
  let _action := invariantQuotientAction (frattini GroupType) invariant
  change QuotientGroup.mk' (frattini GroupType) (conjugator (automorphism (conjugator⁻¹ element))) = _
  have equivariant := invariant_quotient_equivariant (frattini GroupType) invariant
  have first_image : QuotientGroup.mk' (frattini GroupType)
      (conjugator (automorphism (conjugator⁻¹ element))) =
      conjugator • QuotientGroup.mk' (frattini GroupType) (automorphism (conjugator⁻¹ element)) :=
    equivariant conjugator (automorphism (conjugator⁻¹ element))
  have second_image : conjugator • QuotientGroup.mk' (frattini GroupType) (conjugator⁻¹ element) =
      QuotientGroup.mk' (frattini GroupType) element := by
    have result := (equivariant conjugator (conjugator⁻¹ element)).symm
    simpa only [MulAut.smul_def, MulAut.apply_inv_self] using result
  exact first_image.trans ((congrArg (fun value => conjugator • value)
    (member (conjugator⁻¹ element))).trans second_image)

theorem frattini_generators_lift (generators : Subgroup GroupType)
    (full_image : generators.map (QuotientGroup.mk' (frattini GroupType)) = ⊤) : generators = ⊤ := by
  have full := congrArg (Subgroup.comap (QuotientGroup.mk' (frattini GroupType))) full_image
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at full
  exact frattini_nongenerating full

theorem frattini_automorphism_kernel_coprime_subgroup_trivial
    (prime other : ℕ) (prime_prime : prime.Prime) (other_prime : other.Prime) (distinct : prime ≠ other)
    (pgroup : IsPGroup prime GroupType) (actor : Subgroup (MulAut GroupType))
    (actor_le : actor ≤ frattiniAutomorphismKernel GroupType) (actor_pgroup : IsPGroup other actor) :
    actor = ⊥ := by
  let _action := MulDistribMulAction.compHom GroupType actor.subtype
  have invariant : ∀ actorElement : actor, ∀ value ∈ frattini GroupType,
      actorElement • value ∈ frattini GroupType := by
    intro actorElement value member
    exact Subgroup.characteristic_iff_le_comap.mp inferInstance actorElement.val member
  let _quotientAction := invariantQuotientAction (frattini GroupType) invariant
  have quotient_fixed : ∀ actorElement : actor, ∀ value : GroupType ⧸ frattini GroupType,
      actorElement • value = value := by
    intro actorElement value
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective (frattini GroupType) value
    rw [← invariant_quotient_equivariant (frattini GroupType) invariant]
    exact actor_le actorElement.property representative
  have kernel_coprime : Nat.Coprime other (Nat.card (QuotientGroup.mk' (frattini GroupType)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact prime_coprime_pgroup_card other prime other_prime prime_prime (Ne.symm distinct)
      (pgroup.to_subgroup (frattini GroupType))
  have fixed_full_image : (FixedPoints.subgroup actor GroupType).map
      (QuotientGroup.mk' (frattini GroupType)) = ⊤ := by
    apply top_le_iff.mp
    intro value _
    obtain ⟨representative, projection, fixed⟩ := fixed_point_lifts other other_prime actor_pgroup
      (QuotientGroup.mk' (frattini GroupType)) (QuotientGroup.mk'_surjective (frattini GroupType))
      (invariant_quotient_equivariant (frattini GroupType) invariant) kernel_coprime value
      (fun actorElement => quotient_fixed actorElement value)
    exact ⟨representative, fixed, projection⟩
  have fixed_top := frattini_generators_lift _ fixed_full_image
  apply le_bot_iff.mp
  intro automorphism member
  apply Subgroup.mem_bot.mpr
  apply MulEquiv.ext
  intro value
  have value_fixed : value ∈ FixedPoints.subgroup actor GroupType := by rw [fixed_top]; trivial
  exact value_fixed (⟨automorphism, member⟩ : actor)

theorem frattini_automorphism_kernel_pgroup (prime : ℕ) (prime_prime : prime.Prime)
    (pgroup : IsPGroup prime GroupType) : IsPGroup prime (frattiniAutomorphismKernel GroupType) := by
  apply (prime_supported_singleton_iff_pgroup prime prime_prime _).mp
  intro other other_prime divides
  by_contra distinct
  let : Fact other.Prime := ⟨other_prime⟩
  obtain ⟨subgroup, subgroup_card⟩ := Sylow.exists_subgroup_card_pow_prime other
    (G := frattiniAutomorphismKernel GroupType) (n := 1) (by simpa only [pow_one] using divides)
  have subgroup_pgroup : IsPGroup other subgroup := by
    exact IsPGroup.of_card subgroup_card
  let embedded := subgroup.map (frattiniAutomorphismKernel GroupType).subtype
  have embedded_trivial := frattini_automorphism_kernel_coprime_subgroup_trivial prime other
    prime_prime other_prime (Ne.symm distinct) pgroup embedded (Subgroup.map_subtype_le subgroup)
    (subgroup_pgroup.map _)
  have cardinality := congrArg (fun target : Subgroup (MulAut GroupType) => Nat.card target) embedded_trivial
  rw [Subgroup.card_map_of_injective (frattiniAutomorphismKernel GroupType).subtype_injective,
    subgroup_card, Subgroup.card_bot, pow_one] at cardinality
  exact other_prime.ne_one cardinality

end CFSG.SignalizerFunctor.Helpers
