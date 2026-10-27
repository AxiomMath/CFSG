module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartOne.U5K

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem commutatorElement_mul_central_left {z : X} (hz : z ∈ Subgroup.center X) (a b : X) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.1 hz (a * b * a⁻¹)
  calc ⁅z * a, b⁆ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = ⁅a, b⁆ := by
      rw [← h]
      simp [commutatorElement_def, mul_assoc]

theorem commutatorElement_mul_central_right {z : X} (hz : z ∈ Subgroup.center X) (a b : X) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_central_left hz, commutatorElement_inv]

theorem commutator_sup_center_eq_top (h : Group.IsPerfect (X ⧸ Subgroup.center X)) :
    commutator X ⊔ Subgroup.center X = ⊤ := by
  have h1 : (commutator X).map (QuotientGroup.mk' (Subgroup.center X)) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
    rw [← commutator_def]
    exact h.commutator_eq_top
  have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center X)) (commutator X)
  rw [h1, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
  exact h2.symm

theorem isPerfect_commutator (h : Group.IsPerfect (X ⧸ Subgroup.center X)) :
    Group.IsPerfect ↥(commutator X) := by
  rw [Subgroup.isPerfect_iff]
  have hsup := commutator_sup_center_eq_top h
  have hA : ⁅(⊤ : Subgroup X), commutator X⁆ = ⁅commutator X, commutator X⁆ := by
    conv_lhs => rw [← hsup]
    rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq]
  have hB : ⁅commutator X ⊔ Subgroup.center X, (⊤ : Subgroup X)⁆ = commutator X := by
    rw [hsup]
    exact (commutator_def X).symm
  rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq] at hB
  calc ⁅commutator X, commutator X⁆ = ⁅(⊤ : Subgroup X), commutator X⁆ := hA.symm
    _ = ⁅commutator X, (⊤ : Subgroup X)⁆ := Subgroup.commutator_comm _ _
    _ = commutator X := hB

theorem fixed_of_trivial_mod_center (α : MulAut X) (h : ∀ x : X, α x * x⁻¹ ∈ Subgroup.center X) :
    commutator X ≤ (MonoidHom.eqLocus (α : X →* X) (MonoidHom.id X)) := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have ha : α a = (α a * a⁻¹) * a := by group
  have hb : α b = (α b * b⁻¹) * b := by group
  show α ⁅a, b⁆ = ⁅a, b⁆
  rw [map_commutatorElement, ha, hb, commutatorElement_mul_central_left (h a),
    commutatorElement_mul_central_right (h b)]

end CFSG.RankThree.PartOne.U5K
