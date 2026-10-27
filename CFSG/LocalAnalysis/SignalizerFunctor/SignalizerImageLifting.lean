module

public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImages

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

theorem actor_image_injective_of_coprime_kernel [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (homomorphism : GroupType →* ImageType)
    (actor : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (coprime : Nat.Coprime prime (Nat.card homomorphism.ker)) :
    Function.Injective (homomorphism.domRestrict actor) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨exponent, actor_card⟩ := actor_pgroup.exists_card_eq
  have intersection_disjoint : Disjoint homomorphism.ker actor := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [actor_card]
    exact coprime.symm.pow_right exponent
  apply (homomorphism.domRestrict actor).ker_eq_bot_iff.mp
  rw [MonoidHom.ker_domRestrict, Subgroup.subgroupOf_eq_bot]
  exact intersection_disjoint

theorem signalizer_compatible_image_comap (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (kernel_compatible : signalizerCompatible prime rank actor values homomorphism.ker)
    (imageTarget : Subgroup ImageType)
    (image_compatible : signalizerCompatible prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values) imageTarget) :
    signalizerCompatible prime rank actor values (imageTarget.comap homomorphism) := by
  refine ⟨?_, ?_⟩
  · apply Subgroup.le_normalizer_iff.mpr
    intro actorElement actor_member element member
    change homomorphism (actorElement * element * actorElement⁻¹) ∈ imageTarget
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.le_normalizer_iff.mp image_compatible.1 (homomorphism actorElement)
      (Subgroup.mem_map_of_mem homomorphism actor_member) (homomorphism element) member
  · intro subgroup member element element_member
    have image_member := signalizer_image_member prime rank homomorphism actor injective subgroup member
    have image_fixed : homomorphism element ∈
        Subgroup.centralizer (subgroup.map homomorphism : Set ImageType) := by
      apply Subgroup.mem_centralizer_iff.mpr
      rintro imageActor ⟨actorElement, actor_member, rfl⟩
      simpa only [map_mul] using congrArg homomorphism
        (Subgroup.mem_centralizer_iff.mp element_member.2 actorElement actor_member)
    have image_in_value := image_compatible.2 (subgroup.map homomorphism) image_member
      ⟨element_member.1, image_fixed⟩
    rw [signalizer_image_value_of_map homomorphism actor subgroup values injective member.1]
      at image_in_value
    have in_product : element ∈ values subgroup ⊔ homomorphism.ker := by
      rw [← Subgroup.comap_map_eq homomorphism (values subgroup)]
      exact image_in_value
    have fixed_product : element ∈ (homomorphism.ker ⊔ values subgroup) ⊓
        Subgroup.centralizer (subgroup : Set GroupType) :=
      ⟨(sup_comm (values subgroup) homomorphism.ker) ▸ in_product, element_member.2⟩
    rw [centralizer_sup_of_normalizing prime prime_prime subgroup homomorphism.ker
      (values subgroup)
      (elementary_abelian_isPGroup prime subgroup
        (elementary_abelian_of_le prime elementary member.1))
      (member.1.trans kernel_compatible.1) (member.1.trans (normalized subgroup member))
      Subgroup.le_normalizer_of_normal (coprime subgroup member)] at fixed_product
    exact sup_le (kernel_compatible.2 subgroup member)
      (inf_le_left : values subgroup ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤
        values subgroup) fixed_product

theorem signalizer_compatible_image_iff [Finite GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (kernel_compatible : signalizerCompatible prime rank actor values homomorphism.ker)
    (contains_kernel : homomorphism.ker ≤ target) :
    signalizerCompatible prime rank actor values target ↔
      signalizerCompatible prime rank (actor.map homomorphism)
        (signalizerImageValues homomorphism actor values) (target.map homomorphism) := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have kernel_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    rank_large values coprime homomorphism.ker kernel_compatible.1 kernel_compatible.2
  have injective := actor_image_injective_of_coprime_kernel prime prime_prime homomorphism actor
    (elementary_abelian_isPGroup prime actor elementary) kernel_coprime
  constructor
  · intro compatible
    exact signalizer_compatible_image prime rank prime_prime homomorphism actor target elementary
      injective values compatible (signalizer_subgroup_coprime prime rank prime_prime actor
        elementary rank_large values coprime target compatible.1 compatible.2)
  · intro image_compatible
    have compatible := signalizer_compatible_image_comap prime rank prime_prime homomorphism actor
      elementary injective values coprime normalized kernel_compatible
      (target.map homomorphism) image_compatible
    rw [Subgroup.comap_map_eq_self contains_kernel] at compatible
    exact compatible

end CFSG.SignalizerFunctor.Helpers
