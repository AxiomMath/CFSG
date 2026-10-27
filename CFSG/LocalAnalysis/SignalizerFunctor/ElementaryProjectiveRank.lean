module

public import CFSG.LocalAnalysis.SignalizerFunctor.SmallSetPrimeActions
public import CFSG.LocalAnalysis.SignalizerFunctor.ProjectiveTwoPointCyclic
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSetActions

public section

universe fieldUniverse vectorUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]
variable {ActorType : Type actorUniverse} [Group ActorType] [Finite ActorType]

theorem cyclic_prime_exponent_card_dvd
    {GroupType : Type actorUniverse} [Group GroupType] [IsCyclic GroupType]
    (prime : ℕ) (exponent : ∀ element : GroupType, element ^ prime = 1) : Nat.card GroupType ∣ prime := by
  rw [← IsCyclic.exponent_eq_card]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one exponent

theorem linear_projective_two_set_kernel_cyclic [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (invariant : ∀ actor : ActorType, ∀ point : Projectivization FieldType VectorType,
      projectiveLinearAction (action actor) point ∈
        ({first, second} : Set (Projectivization FieldType VectorType)) ↔
      point ∈ ({first, second} : Set (Projectivization FieldType VectorType))) :
    IsCyclic (projectiveLinearAction.comp
      (action.comp (invariantSetPermutation (projectiveLinearAction.comp action)
        ({first, second} : Set (Projectivization FieldType VectorType)) invariant).ker.subtype)).range := by
  let projective := projectiveLinearAction.comp action
  let set_action := invariantSetPermutation projective {first, second} invariant
  let kernel := set_action.ker
  have first_fixed : ∀ actor : kernel, projectiveLinearAction (action actor.val) first = first := by
    intro actor
    have equal := congrArg (fun permutation => (permutation ⟨first, Set.mem_insert _ _⟩).val) actor.property
    exact equal
  have second_fixed : ∀ actor : kernel, projectiveLinearAction (action actor.val) second = second := by
    intro actor
    have equal := congrArg (fun permutation => (permutation ⟨second, Set.mem_insert_of_mem _ rfl⟩).val)
      actor.property
    exact equal
  exact linear_projective_two_point_image_cyclic dimension (action.comp kernel.subtype)
    first second distinct first_fixed second_fixed

omit [Finite ActorType] in
theorem projective_invariant_set_image_kernel
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (points : Set (Projectivization FieldType VectorType))
    (invariant : ∀ actor : ActorType, ∀ point : Projectivization FieldType VectorType,
      projectiveLinearAction (action actor) point ∈ points ↔ point ∈ points) :
    let projective := projectiveLinearAction.comp action
    let image_invariant : ∀ actor : projective.range, ∀ point : Projectivization FieldType VectorType,
        actor.val point ∈ points ↔ point ∈ points := by
      intro actor point
      obtain ⟨source, source_eq⟩ := actor.property
      rw [← source_eq]
      exact invariant source point
    let image_action := invariantSetPermutation projective.range.subtype points image_invariant
    let actor_action := invariantSetPermutation projective points invariant
    (image_action.ker : Subgroup projective.range).map projective.range.subtype =
      (projective.comp actor_action.ker.subtype).range := by
  intro projective image_invariant image_action actor_action
  ext permutation
  constructor
  · rintro ⟨image, image_kernel, rfl⟩
    obtain ⟨actor, actor_eq⟩ := image.property
    have actor_kernel : actor ∈ actor_action.ker := by
      apply Equiv.ext
      intro point
      apply Subtype.ext
      change projective actor point.val = point.val
      rw [actor_eq]
      exact congrArg (fun automorphism : Equiv.Perm points => (automorphism point).val) image_kernel
    exact ⟨⟨actor, actor_kernel⟩, actor_eq⟩
  · rintro ⟨actor, rfl⟩
    refine ⟨⟨projective actor.val, ⟨actor.val, rfl⟩⟩, ?_, rfl⟩
    apply Equiv.ext
    intro point
    apply Subtype.ext
    exact congrArg (fun automorphism : Equiv.Perm points => (automorphism point).val) actor.property

theorem linear_projective_two_set_image_kernel_cyclic [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (invariant : ∀ actor : ActorType, ∀ point : Projectivization FieldType VectorType,
      projectiveLinearAction (action actor) point ∈
        ({first, second} : Set (Projectivization FieldType VectorType)) ↔
      point ∈ ({first, second} : Set (Projectivization FieldType VectorType))) :
    let projective := projectiveLinearAction.comp action
    let image_invariant : ∀ actor : projective.range, ∀ point : Projectivization FieldType VectorType,
        actor.val point ∈ ({first, second} : Set (Projectivization FieldType VectorType)) ↔
          point ∈ ({first, second} : Set (Projectivization FieldType VectorType)) := by
      intro actor point
      obtain ⟨source, source_eq⟩ := actor.property
      rw [← source_eq]
      exact invariant source point
    IsCyclic (invariantSetPermutation projective.range.subtype {first, second} image_invariant).ker := by
  intro projective image_invariant
  let set_action := invariantSetPermutation projective.range.subtype {first, second} image_invariant
  have cyclic := linear_projective_two_set_kernel_cyclic dimension action first second distinct invariant
  have image_eq := projective_invariant_set_image_kernel action {first, second} invariant
  have cyclic_image : IsCyclic (set_action.ker.map projective.range.subtype) := by
    rw [image_eq]
    exact cyclic
  let _cyclic : IsCyclic (projective.range.subtype.comp set_action.ker.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact cyclic_image
  exact isCyclic_of_injective (projective.range.subtype.comp set_action.ker.subtype).rangeRestrict
    (by
      intro first_actor second_actor equal
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun element : (projective.range.subtype.comp set_action.ker.subtype).range => element.val) equal)

theorem elementary_projective_two_set_card_bound [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (prime : ℕ) (prime_prime : prime.Prime)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (exponent : ∀ actor : ActorType, projectiveLinearAction (action actor) ^ prime = 1)
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (invariant : ∀ actor : ActorType, ∀ point : Projectivization FieldType VectorType,
      projectiveLinearAction (action actor) point ∈
        ({first, second} : Set (Projectivization FieldType VectorType)) ↔
      point ∈ ({first, second} : Set (Projectivization FieldType VectorType))) :
    Nat.card (projectiveLinearAction.comp action).range ≤ 2 * prime := by
  classical
  let projective := projectiveLinearAction.comp action
  let _finite : Finite projective.range :=
    Finite.of_surjective projective.rangeRestrict projective.rangeRestrict_surjective
  let points := ({first, second} : Set (Projectivization FieldType VectorType))
  let _finite_points : Finite points := (Set.finite_insert.mpr (Set.finite_singleton second)).to_subtype
  have image_invariant : ∀ actor : projective.range, ∀ point : Projectivization FieldType VectorType,
      actor.val point ∈ points ↔ point ∈ points := by
    intro actor point
    obtain ⟨source, source_eq⟩ := actor.property
    rw [← source_eq]
    exact invariant source point
  let set_action := invariantSetPermutation projective.range.subtype points image_invariant
  let _cyclic : IsCyclic set_action.ker :=
    linear_projective_two_set_image_kernel_cyclic dimension action first second distinct invariant
  have image_exponent : ∀ actor : projective.range, actor ^ prime = 1 := by
    intro actor
    obtain ⟨source, source_eq⟩ := actor.property
    apply Subtype.ext
    change actor.val ^ prime = 1
    rw [← source_eq]
    exact exponent source
  have kernel_exponent : ∀ actor : set_action.ker, actor ^ prime = 1 := by
    intro actor
    apply Subtype.ext
    exact image_exponent actor.val
  have kernel_card_bound : Nat.card set_action.ker ≤ prime :=
    Nat.le_of_dvd prime_prime.pos (cyclic_prime_exponent_card_dvd prime kernel_exponent)
  have set_card : Nat.card points = 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_pair distinct]
  have image_card_bound : Nat.card set_action.range ≤ 2 := by
    have bound := Nat.card_le_card_of_injective set_action.range.subtype Subtype.val_injective
    rw [Nat.card_perm, set_card] at bound
    exact bound
  have quotient_card : Nat.card (projective.range ⧸ set_action.ker) = Nat.card set_action.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange set_action).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup set_action.ker, quotient_card]
  exact Nat.mul_le_mul image_card_bound kernel_card_bound

theorem odd_prime_elementary_projective_two_set_cyclic [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (exponent : ∀ actor : ActorType, projectiveLinearAction (action actor) ^ prime = 1)
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (invariant : ∀ actor : ActorType, ∀ point : Projectivization FieldType VectorType,
      projectiveLinearAction (action actor) point ∈
        ({first, second} : Set (Projectivization FieldType VectorType)) ↔
      point ∈ ({first, second} : Set (Projectivization FieldType VectorType))) :
    IsCyclic (projectiveLinearAction.comp action).range := by
  have small : ({first, second} : Set (Projectivization FieldType VectorType)).ncard < prime := by
    rw [Set.ncard_pair distinct]
    have lower := prime_prime.two_le
    omega
  have fixed : ∀ actor : ActorType, ∀ point ∈ ({first, second} : Set (Projectivization FieldType VectorType)),
      projectiveLinearAction (action actor) point = point := by
    intro actor
    exact prime_power_permutation_small_set_fixed prime prime_prime (projectiveLinearAction (action actor))
      1 (by simpa only [pow_one] using exponent actor) {first, second}
      (Set.finite_insert.mpr (Set.finite_singleton _)) small (invariant actor)
  exact linear_projective_two_point_image_cyclic dimension action first second distinct
    (fun actor => fixed actor first (Set.mem_insert _ _))
    (fun actor => fixed actor second (Set.mem_insert_of_mem _ rfl))

end CFSG.SignalizerFunctor.Helpers
