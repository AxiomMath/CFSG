module

public import CFSG.LocalAnalysis.SignalizerFunctor.SylowNormalizerPromotion
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure

public section

universe groupUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem subgroup_weak_closure_normalizer (target parent : Subgroup GroupType) :
    Subgroup.normalizer (parent : Set GroupType) ≤
      Subgroup.normalizer (subgroupWeakClosure target parent : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator conjugator_member element member
  have map_le : (subgroupWeakClosure target parent).map (MulAut.conj conjugator).toMonoidHom ≤
      subgroupWeakClosure target parent := by
    unfold subgroupWeakClosure
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro original
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro contained
    change conjugateSubgroup conjugator (conjugateSubgroup original target) ≤ _
    rw [conjugate_subgroup_mul]
    apply conjugate_le_weak_closure
    rw [← conjugate_subgroup_mul]
    exact (Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) contained).trans
      (normalized_conjugate_subgroup_le (Subgroup.normalizer (parent : Set GroupType)) parent le_rfl
        conjugator conjugator_member)
  exact map_le (Subgroup.mem_map_of_mem _ member)

theorem subgroup_weak_closure_normal_in_parent (target parent : Subgroup GroupType) :
    ((subgroupWeakClosure target parent).subgroupOf parent).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (subgroup_weak_closure_le target parent)).mpr
    (Subgroup.le_normalizer.trans (subgroup_weak_closure_normalizer target parent))

theorem subgroup_weak_closure_invariant
    {ActorType : Type actorUniverse} [Group ActorType] [MulDistribMulAction ActorType GroupType]
    (target parent : Subgroup GroupType)
    (target_invariant : ∀ actorElement : ActorType, ∀ element ∈ target, actorElement • element ∈ target)
    (parent_invariant : ∀ actorElement : ActorType, ∀ element ∈ parent, actorElement • element ∈ parent) :
    ∀ actorElement : ActorType, ∀ element ∈ subgroupWeakClosure target parent,
      actorElement • element ∈ subgroupWeakClosure target parent := by
  intro actorElement element member
  let homomorphism := MulDistribMulAction.toMonoidHom GroupType actorElement
  have target_equal : target.map homomorphism = target := by
    ext original
    constructor
    · rintro ⟨preimage, preimage_member, rfl⟩
      exact target_invariant actorElement preimage preimage_member
    · intro original_member
      exact ⟨actorElement⁻¹ • original, target_invariant actorElement⁻¹ original original_member,
        smul_inv_smul actorElement original⟩
  have map_le : (subgroupWeakClosure target parent).map homomorphism ≤ subgroupWeakClosure target parent := by
    unfold subgroupWeakClosure
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro conjugator
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro contained
    rw [conjugate_subgroup_map, target_equal]
    apply conjugate_le_weak_closure
    have image_le : (conjugateSubgroup conjugator target).map homomorphism ≤ parent := by
      rintro _ ⟨original, original_member, rfl⟩
      exact parent_invariant actorElement original (contained original_member)
    rwa [conjugate_subgroup_map, target_equal] at image_le
  exact map_le (Subgroup.mem_map_of_mem homomorphism member)

theorem weak_closure_sylow_promotion [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (target parent : Subgroup GroupType)
    (internalSylow : Sylow prime parent)
    (weak_equal : subgroupWeakClosure target ((internalSylow : Subgroup parent).map parent.subtype) =
      subgroupWeakClosure target parent)
    (normalizer_le : Subgroup.normalizer (subgroupWeakClosure target parent : Set GroupType) ≤ parent) :
    ∃ ambientSylow : Sylow prime GroupType,
      (ambientSylow : Subgroup GroupType) = (internalSylow : Subgroup parent).map parent.subtype := by
  apply sylow_of_normalizer_containment prime prime_prime parent internalSylow
  have weak_normalizer := subgroup_weak_closure_normalizer target
    ((internalSylow : Subgroup parent).map parent.subtype)
  rw [weak_equal] at weak_normalizer
  exact weak_normalizer.trans normalizer_le

theorem solvable_matsuyama_complement_core [Finite GroupType] [Group.IsSolvable GroupType]
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (distinct : groupPrime ≠ prime) (sylow : Sylow prime GroupType) (target : Subgroup GroupType)
    (orbit_pgroup : ∀ element : GroupType,
      IsPGroup groupPrime (normalizedConjugateHull (sylow : Subgroup GroupType) (conjugateSubgroup element target))) :
    target ≤ primeSetCore ({prime}ᶜ) := by
  obtain ⟨targetSylow, target_le, normalized⟩ := matsuyama_weak_closure groupPrime groupPrime_prime
    (sylow : Subgroup GroupType) target orbit_pgroup
  have weak_pgroup : IsPGroup groupPrime (subgroupWeakClosure target targetSylow) :=
    targetSylow.isPGroup'.to_le (subgroup_weak_closure_le target targetSylow)
  have weak_coprime : Nat.Coprime prime (Nat.card (subgroupWeakClosure target targetSylow)) :=
    prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct.symm weak_pgroup
  exact (subgroup_le_weak_closure target targetSylow target_le).trans
    (solvable_sylow_normalized_complement_le_core prime prime_prime sylow _ weak_coprime normalized)

end CFSG.SignalizerFunctor.Helpers
