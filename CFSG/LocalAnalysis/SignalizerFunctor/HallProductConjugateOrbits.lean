module

public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality
public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem abelian_product_normal_kernel_conjugate_orbit (parent complement factor kernel orbitActor : Subgroup GroupType)
    (kernel_le : kernel ≤ complement) (kernel_normal : (kernel.subgroupOf complement).Normal)
    (whole : subgroupProduct complement factor = (parent : Set GroupType))
    (abelian : IsMulCommutative factor) (actor_le : orbitActor ≤ factor) (element : parent) :
    ∃ factorElement ∈ factor, normalizedConjugateHull orbitActor (conjugateSubgroup element.val kernel) =
      conjugateSubgroup factorElement (normalizedConjugateHull orbitActor kernel) := by
  let := abelian
  have inverse_member : element.val⁻¹ ∈ parent := parent.inv_mem element.property
  obtain ⟨inverseComplement, inverseComplement_member, inverseFactor, inverseFactor_member, inverseProduct⟩ :=
    (show element.val⁻¹ ∈ subgroupProduct complement factor from whole.symm ▸ inverse_member)
  have normalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer kernel_le).mp kernel_normal
  have kernel_conjugate : conjugateSubgroup element.val kernel = conjugateSubgroup inverseFactor⁻¹ kernel := by
    have inverse_equal : element.val = inverseFactor⁻¹ * inverseComplement⁻¹ := by
      simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv inverseProduct.symm
    rw [inverse_equal, ← conjugate_subgroup_mul]
    have inverse_preserved := Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalizes (complement.inv_mem inverseComplement_member))
    change conjugateSubgroup inverseComplement⁻¹ kernel = kernel at inverse_preserved
    rw [inverse_preserved]
  refine ⟨inverseFactor⁻¹, factor.inv_mem inverseFactor_member, ?_⟩
  rw [kernel_conjugate]
  change (⨆ actorElement : orbitActor, conjugateSubgroup actorElement.val (conjugateSubgroup inverseFactor⁻¹ kernel)) =
    (normalizedConjugateHull orbitActor kernel).map (MulAut.conj inverseFactor⁻¹).toMonoidHom
  unfold normalizedConjugateHull
  rw [Subgroup.map_iSup]
  apply iSup_congr
  intro actorElement
  change conjugateSubgroup actorElement.val (conjugateSubgroup inverseFactor⁻¹ kernel) =
    conjugateSubgroup inverseFactor⁻¹ (conjugateSubgroup actorElement.val kernel)
  rw [conjugate_subgroup_mul, conjugate_subgroup_mul]
  have commute : actorElement.val * inverseFactor⁻¹ = inverseFactor⁻¹ * actorElement.val := by
    exact congrArg (fun internal : factor => internal.val)
      (mul_comm' (⟨actorElement.val, actor_le actorElement.property⟩ : factor)
        (⟨inverseFactor⁻¹, factor.inv_mem inverseFactor_member⟩ : factor))
  rw [commute]

theorem abelian_product_normal_kernel_orbit_pgroup (prime : ℕ)
    (parent complement factor kernel orbitActor : Subgroup GroupType)
    (kernel_le : kernel ≤ complement) (kernel_normal : (kernel.subgroupOf complement).Normal)
    (whole : subgroupProduct complement factor = (parent : Set GroupType))
    (abelian : IsMulCommutative factor) (actor_le : orbitActor ≤ factor)
    (orbit_prime : IsPGroup prime (normalizedConjugateHull orbitActor kernel)) :
    ∀ element : parent, IsPGroup prime (normalizedConjugateHull orbitActor (conjugateSubgroup element.val kernel)) := by
  intro element
  obtain ⟨factorElement, _, equal⟩ := abelian_product_normal_kernel_conjugate_orbit parent complement factor kernel
    orbitActor kernel_le kernel_normal whole abelian actor_le element
  rw [equal]
  exact orbit_prime.map (MulAut.conj factorElement).toMonoidHom

end CFSG.SignalizerFunctor.Helpers
