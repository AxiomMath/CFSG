module

public import CFSG.LocalAnalysis.SignalizerFunctor.StableNormalPGroupActions

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped commutatorElement

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem quotient_centralizer_commutator_le (target acting kernel : Subgroup GroupType)
    [kernel.Normal]
    (contained : target ≤ (Subgroup.centralizer
      (acting.map (QuotientGroup.mk' kernel) : Set (GroupType ⧸ kernel))).comap (QuotientGroup.mk' kernel)) :
    ⁅target, acting⁆ ≤ kernel := by
  apply Subgroup.commutator_le.mpr
  intro first first_member second second_member
  let projection := QuotientGroup.mk' kernel
  have commute_eq := Subgroup.mem_centralizer_iff.mp (contained first_member) (projection second)
    (Subgroup.mem_map_of_mem projection second_member)
  change projection second * projection first = projection first * projection second at commute_eq
  have commutator_one : projection ⁅first, second⁆ = 1 := by
    simp only [commutatorElement_def, map_mul, map_inv]
    rw [← commute_eq]
    group
  exact (QuotientGroup.eq_one_iff _).mp commutator_one

variable [Finite GroupType]

theorem zj_growth_closure_class_two_properties (prime : ℕ) (prime_prime : prime.Prime)
    (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) (kernel : Subgroup GroupType) [kernel.Normal]
    (proper : kernel < embeddedOrderThompsonCenter (sylow : Subgroup GroupType)) :
    kernel < zjGrowthClosure (sylow : Subgroup GroupType) kernel ∧
      zjGrowthClosure (sylow : Subgroup GroupType) kernel ≤ primeSetCore {prime} ∧
      ⁅zjGrowthClosure (sylow : Subgroup GroupType) kernel, primeSetCore {prime}⁆ ≤ kernel ∧
      ⁅zjGrowthClosure (sylow : Subgroup GroupType) kernel,
        zjGrowthClosure (sylow : Subgroup GroupType) kernel⁆ ≤ kernel ∧
      kernel ≤ Subgroup.centralizer (zjGrowthClosure (sylow : Subgroup GroupType) kernel : Set GroupType) := by
  let base : Subgroup GroupType := sylow
  let fixed := zjGrowthFixedSubgroup base kernel
  let closure := zjGrowthClosure base kernel
  let core := primeSetCore (GroupType := GroupType) {prime}
  let _coreNormal := prime_set_core_normal (GroupType := GroupType) {prime}
  have properties := zj_growth_fixed_subgroup_properties prime prime_prime base kernel sylow.isPGroup' proper
  have core_containment := zj_growth_closure_le_prime_core prime prime_prime stable self_centralizing sylow
    kernel proper
  have core_le : core ≤ base := (prime_core_isPGroup prime prime_prime).le_sylow_of_normal sylow
  let centralizer := (Subgroup.centralizer
    (core.map (QuotientGroup.mk' kernel) : Set (GroupType ⧸ kernel))).comap (QuotientGroup.mk' kernel)
  let _imageNormal := _coreNormal.map (QuotientGroup.mk' kernel) (QuotientGroup.mk'_surjective kernel)
  have centralizer_normal : centralizer.Normal := inferInstance
  have fixed_centralizes_core : fixed ≤ centralizer := by
    exact inf_le_right.trans (Subgroup.comap_mono
      (Subgroup.centralizer_le (Subgroup.map_mono core_le)))
  have closure_centralizes_core : closure ≤ centralizer := normalized_conjugate_hull_le ⊤ _ _
    fixed_centralizes_core (by let := centralizer_normal; exact Subgroup.le_normalizer_of_normal)
  have commutator_le := quotient_centralizer_commutator_le closure core kernel closure_centralizes_core
  have closure_centralizes_kernel : closure ≤ Subgroup.centralizer (kernel : Set GroupType) := by
    let := properties.2.2.1
    have fixed_centralizes_kernel : fixed ≤ Subgroup.centralizer (kernel : Set GroupType) :=
      (Subgroup.le_centralizer fixed).trans (Subgroup.centralizer_le properties.1.le)
    exact normalized_conjugate_hull_le ⊤ _ _ fixed_centralizes_kernel Subgroup.le_normalizer_of_normal
  refine ⟨properties.1.trans_le (subgroup_le_normalized_conjugate_hull ⊤ fixed),
    core_containment.2, commutator_le,
    (Subgroup.commutator_mono le_rfl core_containment.2).trans commutator_le, ?_⟩
  exact Subgroup.le_centralizer_iff.mp closure_centralizes_kernel

end CFSG.SignalizerFunctor.Helpers
