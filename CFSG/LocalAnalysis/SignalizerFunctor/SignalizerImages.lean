module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageIndices

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]

theorem signalizer_image_properties (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other) :
    (∀ subgroup ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      signalizerImageValues homomorphism actor values subgroup ≤
        Subgroup.centralizer (subgroup : Set ImageType) ∧
      Nat.Coprime prime (Nat.card (signalizerImageValues homomorphism actor values subgroup)) ∧
      actor.map homomorphism ≤ Subgroup.normalizer
        (signalizerImageValues homomorphism actor values subgroup : Set ImageType)) ∧
    (∀ subgroup ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      ∀ other ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
        signalizerImageValues homomorphism actor values subgroup ⊓
          Subgroup.centralizer (other : Set ImageType) ≤
            signalizerImageValues homomorphism actor values other) := by
  refine ⟨?_, ?_⟩
  · intro subgroup member
    let selected := signalizerImageIndex homomorphism actor subgroup
    have selected_member := signalizer_image_index_member prime rank homomorphism actor
      injective subgroup member
    have selected_map := signalizer_image_index_map homomorphism actor subgroup member.1
    refine ⟨?_, (coprime selected selected_member).of_dvd_right
      (Subgroup.card_map_dvd (values selected) homomorphism),
      normalizer_image_le homomorphism actor (values selected)
        (normalized selected selected_member)⟩
    change (values selected).map homomorphism ≤ Subgroup.centralizer (subgroup : Set ImageType)
    conv_rhs => rw [← selected_map]
    rintro imageElement ⟨element, element_member, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    rintro imageActor ⟨actorElement, actor_member, rfl⟩
    simpa only [map_mul] using congrArg homomorphism
      (Subgroup.mem_centralizer_iff.mp (central selected selected_member element_member)
        actorElement actor_member)
  · intro subgroup member other other_member
    let selected := signalizerImageIndex homomorphism actor subgroup
    let otherSelected := signalizerImageIndex homomorphism actor other
    have selected_member := signalizer_image_index_member prime rank homomorphism actor
      injective subgroup member
    have other_selected_member := signalizer_image_index_member prime rank homomorphism actor
      injective other other_member
    change (values selected).map homomorphism ⊓ Subgroup.centralizer (other : Set ImageType) ≤
      (values otherSelected).map homomorphism
    rw [← signalizer_image_index_map homomorphism actor other other_member.1,
      ← coprime_centralizer_image prime prime_prime homomorphism otherSelected (values selected)
        (elementary_abelian_isPGroup prime otherSelected
          (elementary_abelian_of_le prime elementary other_selected_member.1))
        (other_selected_member.1.trans (normalized selected selected_member))
        (coprime selected selected_member)]
    exact Subgroup.map_mono (balanced selected selected_member otherSelected other_selected_member)

theorem signalizer_image_solvable (prime rank : ℕ)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType)
    (solvable : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Group.IsSolvable (values subgroup)) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      Group.IsSolvable (signalizerImageValues homomorphism actor values subgroup) := by
  intro subgroup member
  let selected := signalizerImageIndex homomorphism actor subgroup
  let := solvable selected
    (signalizer_image_index_member prime rank homomorphism actor injective subgroup member)
  exact Group.isSolvable_of_surjective
    (subgroup_image_hom_surjective homomorphism (values selected))

theorem signalizer_image_supported (prime rank : ℕ)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (supported : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      primeSupported primes (Nat.card (values subgroup))) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      primeSupported primes (Nat.card (signalizerImageValues homomorphism actor values subgroup)) := by
  intro subgroup member
  exact prime_supported_of_dvd primes
    (supported _ (signalizer_image_index_member prime rank homomorphism actor injective
      subgroup member)) (Subgroup.card_map_dvd _ homomorphism)

theorem signalizer_compatible_image (prime rank : ℕ) (prime_prime : prime.Prime)
    (homomorphism : GroupType →* ImageType) (actor target : Subgroup GroupType)
    (elementary : IsElemAbelian prime actor)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType)
    (compatible : signalizerCompatible prime rank actor values target)
    (coprime : Nat.Coprime prime (Nat.card target)) :
    signalizerCompatible prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values) (target.map homomorphism) := by
  refine ⟨normalizer_image_le homomorphism actor target compatible.1, ?_⟩
  intro subgroup member
  let selected := signalizerImageIndex homomorphism actor subgroup
  have selected_member := signalizer_image_index_member prime rank homomorphism actor
    injective subgroup member
  change target.map homomorphism ⊓ Subgroup.centralizer (subgroup : Set ImageType) ≤
    (values selected).map homomorphism
  rw [← signalizer_image_index_map homomorphism actor subgroup member.1,
    ← coprime_centralizer_image prime prime_prime homomorphism selected target
      (elementary_abelian_isPGroup prime selected
        (elementary_abelian_of_le prime elementary selected_member.1))
      (selected_member.1.trans compatible.1) coprime]
  exact Subgroup.map_mono (compatible.2 selected selected_member)

theorem signalizer_image_completion (prime rank : ℕ)
    (homomorphism : GroupType →* ImageType) (actor : Subgroup GroupType)
    (injective : Function.Injective (homomorphism.domRestrict actor))
    (values : Subgroup GroupType → Subgroup GroupType) :
    (⨆ selected ∈ signalizerFunctorEk prime rank (actor.map homomorphism),
      signalizerImageValues homomorphism actor values selected) =
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected).map homomorphism := by
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact le_iSup_of_le (signalizerImageIndex homomorphism actor selected)
      (le_iSup_of_le
        (signalizer_image_index_member prime rank homomorphism actor injective selected member)
        le_rfl)
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    rw [← signalizer_image_value_of_map homomorphism actor selected values injective member.1]
    exact signalizer_value_le_completion prime rank (actor.map homomorphism)
      (signalizerImageValues homomorphism actor values)
      (signalizer_image_member prime rank homomorphism actor injective selected member)

end CFSG.SignalizerFunctor.Helpers
