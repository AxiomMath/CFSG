module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageIndices
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableNormalProducts

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def primeSetCore (primes : Set ℕ) : Subgroup GroupType :=
  ⨆ (candidate : Subgroup GroupType)
    (_ : candidate.Normal ∧ primeSupported primes (Nat.card candidate)), candidate

theorem prime_set_core_contains (primes : Set ℕ) (candidate : Subgroup GroupType)
    (normal : candidate.Normal) (supported : primeSupported primes (Nat.card candidate)) :
    candidate ≤ primeSetCore primes :=
  le_iSup_of_le candidate (le_iSup_of_le ⟨normal, supported⟩ le_rfl)

theorem prime_set_core_normal (primes : Set ℕ) :
    (primeSetCore (GroupType := GroupType) primes).Normal := by
  let candidates := {candidate : Subgroup GroupType //
    candidate.Normal ∧ primeSupported primes (Nat.card candidate)}
  let _candidateNormal : ∀ candidate : candidates, candidate.val.Normal :=
    fun candidate => candidate.property.1
  have normal : (⨆ candidate : candidates, candidate.val).Normal := inferInstance
  have equal : (⨆ candidate : candidates, candidate.val) = primeSetCore primes := by
    exact iSup_subtype
  rwa [equal] at normal

theorem prime_set_core_supported [Finite GroupType] (primes : Set ℕ) :
    primeSupported primes (Nat.card (primeSetCore (GroupType := GroupType) primes)) := by
  classical
  let candidates := {candidate : Subgroup GroupType //
    candidate.Normal ∧ primeSupported primes (Nat.card candidate)}
  let _candidateFintype := Fintype.ofFinite candidates
  have finite_join : (Finset.univ : Finset candidates).sup (fun candidate => candidate.val) =
      primeSetCore primes := by
    rw [Finset.sup_univ_eq_iSup]
    exact iSup_subtype
  rw [← finite_join]
  have property : ∀ finiteSet : Finset candidates,
      ((finiteSet.sup (fun candidate => candidate.val)).Normal ∧
        primeSupported primes (Nat.card
          (finiteSet.sup (fun candidate => candidate.val) : Subgroup GroupType))) := by
    intro finiteSet
    induction finiteSet using Finset.induction_on with
    | empty =>
      simp only [Finset.sup_empty]
      exact ⟨inferInstance, by rw [Subgroup.card_bot]; exact prime_supported_one primes⟩
    | @insert candidate finiteSet not_member induction_hypothesis =>
      rw [Finset.sup_insert]
      let := candidate.property.1
      let := induction_hypothesis.1
      exact ⟨inferInstance, prime_supported_sup_of_normalizing primes _ _
        Subgroup.le_normalizer_of_normal candidate.property.2 induction_hypothesis.2⟩
  exact (property Finset.univ).2

theorem prime_set_core_map_equiv [Finite GroupType] (primes : Set ℕ)
    (automorphism : GroupType ≃* GroupType) :
    (primeSetCore primes).map automorphism.toMonoidHom = primeSetCore primes := by
  have map_le : ∀ equivalence : GroupType ≃* GroupType,
      (primeSetCore primes).map equivalence.toMonoidHom ≤ primeSetCore primes := by
    intro equivalence
    apply prime_set_core_contains
    · exact (prime_set_core_normal primes).map equivalence.toMonoidHom equivalence.surjective
    · rw [Subgroup.card_map_of_injective equivalence.injective]
      exact prime_set_core_supported primes
  apply le_antisymm (map_le automorphism)
  have inverse_le := Subgroup.map_mono (f := automorphism.toMonoidHom) (map_le automorphism.symm)
  rw [Subgroup.map_map] at inverse_le
  have composition : automorphism.toMonoidHom.comp automorphism.symm.toMonoidHom =
      MonoidHom.id GroupType := by
    ext element
    exact automorphism.apply_symm_apply element
  rwa [composition, Subgroup.map_id] at inverse_le

theorem prime_set_core_characteristic [Finite GroupType] (primes : Set ℕ) :
    (primeSetCore (GroupType := GroupType) primes).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr (prime_set_core_map_equiv primes)

theorem prime_set_core_quotient_trivial [Finite GroupType] (primes : Set ℕ) :
    let core := primeSetCore (GroupType := GroupType) primes
    let _normal := prime_set_core_normal (GroupType := GroupType) primes
    primeSetCore (GroupType := GroupType ⧸ core) primes = ⊥ := by
  let core := primeSetCore (GroupType := GroupType) primes
  let _normal := prime_set_core_normal (GroupType := GroupType) primes
  let quotientCore := primeSetCore (GroupType := GroupType ⧸ core) primes
  let projection := QuotientGroup.mk' core
  have preimage_normal : (quotientCore.comap projection).Normal := by
    let := prime_set_core_normal (GroupType := GroupType ⧸ core) primes
    infer_instance
  have contains_core : core ≤ quotientCore.comap projection := by
    intro element member
    change projection element ∈ quotientCore
    have trivial : projection element = 1 := (QuotientGroup.eq_one_iff _).mpr member
    rw [trivial]
    exact quotientCore.one_mem
  let restricted := subgroupImageHom projection (quotientCore.comap projection)
  have image_eq : (quotientCore.comap projection).map projection = quotientCore :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective core) quotientCore
  have preimage_supported : primeSupported primes (Nat.card (quotientCore.comap projection)) := by
    have kernel_supported : primeSupported primes (Nat.card restricted.ker) := by
      have kernel_embeds : restricted.ker.map (quotientCore.comap projection).subtype ≤ core := by
        rintro element ⟨representative, member, rfl⟩
        apply (QuotientGroup.eq_one_iff _).mp
        exact congrArg Subtype.val member
      have supported_image := prime_supported_of_dvd primes (prime_set_core_supported primes)
        (Subgroup.card_dvd_of_le kernel_embeds)
      rwa [Subgroup.card_map_of_injective (quotientCore.comap projection).subtype_injective]
        at supported_image
    have image_supported : primeSupported primes
        (Nat.card ((quotientCore.comap projection).map projection)) := by
      rw [image_eq]
      exact prime_set_core_supported primes
    have card_formula := restricted.ker.card_mul_index
    rw [Subgroup.index_ker] at card_formula
    have range_top : restricted.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (subgroup_image_hom_surjective projection _)
    rw [range_top, Subgroup.card_top] at card_formula
    rw [← card_formula]
    exact prime_supported_mul primes kernel_supported image_supported
  have preimage_le := prime_set_core_contains primes (quotientCore.comap projection)
    preimage_normal preimage_supported
  have image_le := Subgroup.map_mono (f := projection) preimage_le
  rw [image_eq] at image_le
  have mapped_core : core.map projection = ⊥ := by
    change core.map (QuotientGroup.mk' core) = ⊥
    exact (Subgroup.map_eq_bot_iff core).mpr (by rw [QuotientGroup.ker_mk'])
  rw [mapped_core] at image_le
  exact le_bot_iff.mp image_le

end CFSG.SignalizerFunctor.Helpers
