module

public import CFSG.LocalAnalysis.SignalizerFunctor.QuadraticEndomorphisms
public import CFSG.LocalAnalysis.SignalizerFunctor.LinearInvariantActions

public section

universe fieldUniverse vectorUniverse actorUniverse firstUniverse secondUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem pgroup_direct_product (prime : ℕ)
    {FirstType : Type firstUniverse} [Group FirstType]
    {SecondType : Type secondUniverse} [Group SecondType]
    (first_pgroup : IsPGroup prime FirstType) (second_pgroup : IsPGroup prime SecondType) :
    IsPGroup prime (FirstType × SecondType) := by
  intro element
  obtain ⟨first_exponent, first_power⟩ := first_pgroup element.1
  obtain ⟨second_exponent, second_power⟩ := second_pgroup element.2
  refine ⟨first_exponent + second_exponent, ?_⟩
  apply Prod.ext
  · change element.1 ^ (prime ^ (first_exponent + second_exponent)) = 1
    rw [pow_add, pow_mul, first_power, one_pow]
  · change element.2 ^ (prime ^ (first_exponent + second_exponent)) = 1
    rw [pow_add, Nat.mul_comm, pow_mul, second_power, one_pow]

theorem pgroup_of_kernel_and_range (prime : ℕ)
    {FirstType : Type firstUniverse} [Group FirstType]
    {SecondType : Type secondUniverse} [Group SecondType]
    (homomorphism : FirstType →* SecondType)
    (kernel_pgroup : IsPGroup prime homomorphism.ker)
    (range_pgroup : IsPGroup prime homomorphism.range) : IsPGroup prime FirstType := by
  intro element
  obtain ⟨image_exponent, image_power⟩ := range_pgroup ⟨homomorphism element, ⟨element, rfl⟩⟩
  have image_trivial : homomorphism (element ^ (prime ^ image_exponent)) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val image_power
  obtain ⟨kernel_exponent, kernel_power⟩ :=
    kernel_pgroup ⟨element ^ (prime ^ image_exponent), image_trivial⟩
  refine ⟨image_exponent + kernel_exponent, ?_⟩
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val kernel_power

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]
variable {ActorType : Type actorUniverse} [Group ActorType]

theorem quadratic_linear_automorphism_prime_power (prime : ℕ) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0) : automorphism ^ prime = 1 := by
  have power := square_zero_one_add_power (automorphism.toLinearMap - 1) quadratic prime
  have one_add : 1 + (automorphism.toLinearMap - 1) = automorphism.toLinearMap := by noncomm_ring
  have cast_zero : (prime : Module.End FieldType VectorType) = 0 := by
    ext vector
    simp only [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul FieldType,
      CharP.cast_eq_zero FieldType prime, zero_smul, LinearMap.zero_apply]
  rw [one_add, cast_zero, zero_mul, add_zero] at power
  let homomorphism := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    (R := FieldType) (M := VectorType)
  have image_power : homomorphism (automorphism ^ prime) = homomorphism 1 := by
    simpa only [map_pow, map_one, homomorphism,
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using power
  apply LinearEquiv.ext
  intro vector
  exact congrArg (fun operator : Module.End FieldType VectorType => operator vector) image_power

theorem invariant_linear_joint_kernel_quadratic
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace)
    (actor : ActorType)
    (restriction_identity : invariantLinearRestriction action subspace invariant actor = 1)
    (quotient_identity : invariantLinearQuotient action subspace invariant actor = 1) :
    ((action actor).toLinearMap - 1) ^ 2 = 0 := by
  have differences_mem : ∀ vector : VectorType, action actor vector - vector ∈ subspace := by
    intro vector
    apply (Submodule.Quotient.eq subspace).mp
    have identity := congrArg (fun automorphism => automorphism (subspace.mkQ vector)) quotient_identity
    rwa [invariant_linear_quotient_apply, LinearEquiv.coe_one, id_eq] at identity
  have fixes_subspace : ∀ vector ∈ subspace, action actor vector = vector := by
    intro vector vector_mem
    have identity := congrArg (fun automorphism => (automorphism ⟨vector, vector_mem⟩).val)
      restriction_identity
    rwa [invariant_linear_restriction_apply, LinearEquiv.coe_one, id_eq] at identity
  ext vector
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  exact sub_eq_zero.mpr (fixes_subspace _ (differences_mem vector))

theorem faithful_invariant_linear_joint_kernel_pgroup
    (prime : ℕ) [CharP FieldType prime]
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (faithful : Function.Injective action)
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace) :
    IsPGroup prime ((invariantLinearRestriction action subspace invariant).prod
      (invariantLinearQuotient action subspace invariant)).ker := by
  intro actor
  have identities := actor.property
  have restriction_identity : invariantLinearRestriction action subspace invariant actor.val = 1 :=
    congrArg Prod.fst identities
  have quotient_identity : invariantLinearQuotient action subspace invariant actor.val = 1 :=
    congrArg Prod.snd identities
  have power := quadratic_linear_automorphism_prime_power prime (action actor.val)
    (invariant_linear_joint_kernel_quadratic action subspace invariant actor.val
      restriction_identity quotient_identity)
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply faithful
  simpa only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one] using power

theorem faithful_linear_prime_extension
    (prime : ℕ) [CharP FieldType prime]
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (faithful : Function.Injective action)
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace)
    (restriction_pgroup : IsPGroup prime (invariantLinearRestriction action subspace invariant).range)
    (quotient_pgroup : IsPGroup prime (invariantLinearQuotient action subspace invariant).range) :
    IsPGroup prime ActorType := by
  let restriction := invariantLinearRestriction action subspace invariant
  let quotient := invariantLinearQuotient action subspace invariant
  let joint := restriction.prod quotient
  have product_pgroup := pgroup_direct_product prime restriction_pgroup quotient_pgroup
  let image : joint.range →* restriction.range × quotient.range := {
    toFun actor := ⟨⟨actor.val.1, by
      obtain ⟨source, source_eq⟩ := actor.property
      exact ⟨source, congrArg Prod.fst source_eq⟩⟩, ⟨actor.val.2, by
      obtain ⟨source, source_eq⟩ := actor.property
      exact ⟨source, congrArg Prod.snd source_eq⟩⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have image_injective : Function.Injective image := by
    intro first second equal
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun value => value.1.val) equal
    · exact congrArg (fun value => value.2.val) equal
  exact pgroup_of_kernel_and_range prime joint
    (faithful_invariant_linear_joint_kernel_pgroup prime action faithful subspace invariant)
    (product_pgroup.of_injective image image_injective)

end CFSG.SignalizerFunctor.Helpers
