module

public import Mathlib.GroupTheory.IsPerfect

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

variable {G : Type*} [Group G]

lemma commutatorElement_mul_central_left {t s c : G} (hc : c ∈ Subgroup.center G) :
    ⁅t * c, s⁆ = ⁅t, s⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc t * c * s * (c⁻¹ * t⁻¹) * s⁻¹
      = t * (c * s) * (c⁻¹ * t⁻¹) * s⁻¹ := by group
    _ = t * (s * c) * (c⁻¹ * t⁻¹) * s⁻¹ := by rw [Subgroup.mem_center_iff.mp hc s]
    _ = t * s * t⁻¹ * s⁻¹ := by group

lemma commutatorElement_mul_central_right {s t c : G} (hc : c ∈ Subgroup.center G) :
    ⁅s, t * c⁆ = ⁅s, t⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc s * (t * c) * s⁻¹ * (c⁻¹ * t⁻¹)
      = s * t * (c * s⁻¹) * (c⁻¹ * t⁻¹) := by group
    _ = s * t * (s⁻¹ * c) * (c⁻¹ * t⁻¹) := by rw [Subgroup.mem_center_iff.mp hc s⁻¹]
    _ = s * t * s⁻¹ * t⁻¹ := by group

theorem le_of_isPerfect_of_le_sup_center {T C K : Subgroup G}
    (hT : Group.IsPerfect T) (hC : C ≤ Subgroup.center G) (hK : Group.IsPerfect K)
    (hKTC : K ≤ T ⊔ C) : K ≤ T := by
  have : C.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hC hn) g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hTC : ⁅T ⊔ C, T ⊔ C⁆ ≤ ⁅T, T⁆ := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨t, ht, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    obtain ⟨t', ht', c', hc', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
    have e : ⁅t * c, t' * c'⁆ = ⁅t, t'⁆ := by
      rw [commutatorElement_mul_central_left (hC hc),
        commutatorElement_mul_central_right (hC hc')]
    rw [e]
    exact Subgroup.commutator_mem_commutator ht ht'
  have hKK : ⁅K, K⁆ ≤ ⁅T ⊔ C, T ⊔ C⁆ := Subgroup.commutator_mono hKTC hKTC
  calc K = ⁅K, K⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ ⁅T, T⁆ := hKK.trans hTC
    _ = T := Subgroup.commutator_eq_self

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
