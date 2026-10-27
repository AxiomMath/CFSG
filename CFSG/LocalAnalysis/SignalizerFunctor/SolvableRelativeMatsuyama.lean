module

public import CFSG.LocalAnalysis.SignalizerFunctor.WeakClosureControl
public import CFSG.LocalAnalysis.SignalizerFunctor.RelativeWeakClosure
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductConjugateOrbits

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem solvable_normalized_matsuyama_core (prime groupPrime : ℕ)
    (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime) (distinct : groupPrime ≠ prime)
    (parent target : Subgroup GroupType) (parent_solvable : Group.IsSolvable parent)
    (target_le : target ≤ parent) (sylow : Sylow prime parent)
    (orbit_pgroup : ∀ element : parent,
      IsPGroup groupPrime (normalizedConjugateHull ((sylow : Subgroup parent).map parent.subtype)
        (conjugateSubgroup element.val target))) :
    target ≤ (primeSetCore (GroupType := parent) ({prime}ᶜ)).map parent.subtype := by
  let := parent_solvable
  have internal_orbits : ∀ element : parent, IsPGroup groupPrime
      (normalizedConjugateHull (sylow : Subgroup parent)
        (conjugateSubgroup element (target.subgroupOf parent))) := by
    intro element
    let orbit := normalizedConjugateHull (sylow : Subgroup parent)
      (conjugateSubgroup element (target.subgroupOf parent))
    have mapped_equal : orbit.map parent.subtype =
        normalizedConjugateHull ((sylow : Subgroup parent).map parent.subtype)
          (conjugateSubgroup element.val target) := by
      rw [normalized_conjugate_hull_map, conjugate_subgroup_map, Subgroup.map_subgroupOf_eq_of_le target_le]
      rfl
    have mapped_prime : IsPGroup groupPrime (orbit.map parent.subtype) := by
      rw [mapped_equal]
      exact orbit_pgroup element
    exact mapped_prime.of_equiv (orbit.equivMapOfInjective parent.subtype parent.subtype_injective).symm
  have contained := solvable_matsuyama_complement_core prime groupPrime prime_prime groupPrime_prime distinct sylow
    (target.subgroupOf parent) internal_orbits
  have mapped := Subgroup.map_mono (f := parent.subtype) contained
  rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped

theorem abelian_product_conjugates_le_local_core (prime kernelPrime : ℕ)
    (prime_prime : prime.Prime) (kernelPrime_prime : kernelPrime.Prime) (distinct : kernelPrime ≠ prime)
    (parent complement factor kernel localParent subgroup : Subgroup GroupType)
    (kernel_le : kernel ≤ complement) (kernel_normal : (kernel.subgroupOf complement).Normal)
    (whole : subgroupProduct complement factor = (parent : Set GroupType)) (abelian : IsMulCommutative factor)
    (local_le : localParent ≤ parent) (local_solvable : Group.IsSolvable localParent)
    (subgroup_prime : IsPGroup kernelPrime subgroup) (kernel_subgroup : kernel ≤ subgroup)
    (subgroup_normalized : localParent ≤ Subgroup.normalizer (subgroup : Set GroupType))
    (sylow : Sylow prime localParent) (sylow_factor : (sylow : Subgroup localParent).map localParent.subtype ≤ factor) :
    relativeWeakClosure parent kernel localParent ≤
      (primeSetCore (GroupType := localParent) ({prime}ᶜ)).map localParent.subtype := by
  let sylowActor := (sylow : Subgroup localParent).map localParent.subtype
  have base_orbit : IsPGroup kernelPrime (normalizedConjugateHull sylowActor kernel) :=
    subgroup_prime.to_le (normalized_conjugate_hull_le sylowActor kernel subgroup kernel_subgroup
      ((Subgroup.map_subtype_le _).trans subgroup_normalized))
  have parent_orbits := abelian_product_normal_kernel_orbit_pgroup kernelPrime parent complement factor kernel
    sylowActor kernel_le kernel_normal whole abelian sylow_factor base_orbit
  apply iSup_le
  intro conjugator
  apply iSup_le
  intro contained
  apply solvable_normalized_matsuyama_core prime kernelPrime prime_prime kernelPrime_prime distinct localParent
    (conjugateSubgroup conjugator.val kernel) local_solvable contained sylow
  intro localElement
  rw [conjugate_subgroup_mul]
  exact parent_orbits ⟨localElement.val * conjugator.val, parent.mul_mem (local_le localElement.property) conjugator.property⟩

end CFSG.SignalizerFunctor.Helpers
