module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

theorem normalizer_image_le (homomorphism : GroupType →* ImageType)
    (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    actor.map homomorphism ≤ Subgroup.normalizer (target.map homomorphism : Set ImageType) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro imageActor ⟨actorElement, actor_member, rfl⟩ imageElement
    ⟨element, member, rfl⟩
  refine ⟨actorElement * element * actorElement⁻¹,
    Subgroup.le_normalizer_iff.mp normalized actorElement actor_member element member, ?_⟩
  simp only [map_mul, map_inv]

theorem coprime_centralizer_image (prime : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    (target ⊓ Subgroup.centralizer (actor : Set GroupType)).map homomorphism =
      target.map homomorphism ⊓
        Subgroup.centralizer (actor.map homomorphism : Set ImageType) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _action := conjugationAction actor target normalized
  apply le_antisymm
  · rintro imageElement ⟨element, member, rfl⟩
    refine ⟨⟨element, member.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro imageActor ⟨actorElement, actor_member, rfl⟩
    simpa only [map_mul] using congrArg homomorphism
      (Subgroup.mem_centralizer_iff.mp member.2 actorElement actor_member)
  · intro imageElement member
    obtain ⟨element, element_member, image_eq⟩ := member.1
    let restricted := homomorphism.domRestrict target
    let fibre : SubMulAction actor target :=
      ⟨{representative | restricted representative = imageElement}, by
        intro actorElement representative representative_member
        change homomorphism (actorElement.val * representative.val * actorElement.val⁻¹) =
          imageElement
        rw [map_mul, map_mul, map_inv]
        change homomorphism actorElement.val * restricted representative *
          (homomorphism actorElement.val)⁻¹ = imageElement
        rw [representative_member]
        have commutes := Subgroup.mem_centralizer_iff.mp member.2
          (homomorphism actorElement.val)
          (Subgroup.mem_map_of_mem homomorphism actorElement.property)
        rw [commutes, mul_assoc, mul_inv_cancel, mul_one]⟩
    have fibre_card : Nat.card fibre = Nat.card restricted.ker := by
      have fibre_eq : {representative : target | restricted representative = imageElement} =
          restricted ⁻¹' {restricted (⟨element, element_member⟩ : target)} := by
        ext representative
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change (restricted representative = imageElement) ↔
          restricted representative = homomorphism element
        rw [image_eq]
      exact (Nat.card_congr (Set.equivOfEq fibre_eq)).trans
        (Nat.card_congr (restricted.fiberEquivKer (⟨element, element_member⟩ : target)))
    have not_divides : ¬ prime ∣ Nat.card fibre := by
      rw [fibre_card]
      exact prime_prime.coprime_iff_not_dvd.mp
        (coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card restricted.ker))
    obtain ⟨representative, fixed⟩ :=
      actor_pgroup.nonempty_fixed_point_of_prime_not_dvd_card fibre not_divides
    refine ⟨representative.val.val, ⟨representative.val.property, ?_⟩,
      representative.property⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement actor_member
    have equality := congrArg (fun fixedElement : fibre => fixedElement.val.val)
      (fixed (⟨actorElement, actor_member⟩ : actor))
    change actorElement * representative.val.val * actorElement⁻¹ = representative.val.val
      at equality
    exact mul_inv_eq_iff_eq_mul.mp equality

theorem coprime_centralizer_image_elementary (prime : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    (target ⊓ Subgroup.centralizer (actor : Set GroupType)).map homomorphism =
      target.map homomorphism ⊓
        Subgroup.centralizer (actor.map homomorphism : Set ImageType) := by
  exact coprime_centralizer_image prime prime_prime homomorphism actor target
    (elementary_abelian_isPGroup prime actor elementary) normalized coprime

end CFSG.SignalizerFunctor.Helpers
