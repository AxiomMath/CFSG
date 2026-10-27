module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentT
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiagA5
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem exists_mem_A_conj_v_eq_w : ∃ g ∈ D.A, g⁻¹ * D.v * g = D.w := by
  obtain ⟨g, hg⟩ := exists_conj_hM_of_sq_eq_neg_one cM_sq
  refine ⟨D.d g, ⟨g, rfl⟩, ?_⟩
  have hgc : g⁻¹ * hM * g = cM := by rw [← hg]; group
  calc (D.d g)⁻¹ * D.v * D.d g = (D.d g)⁻¹ * D.d hM * D.d g := rfl
    _ = D.d (g⁻¹ * hM * g) := by rw [map_mul, map_mul, map_inv]
    _ = D.d cM := by rw [hgc]
    _ = D.w := rfl

theorem exists_mem_A_conj_v_eq_v_mul_w : ∃ g ∈ D.A, g⁻¹ * D.v * g = D.v * D.w := by
  obtain ⟨g, hg⟩ := exists_conj_hM_of_sq_eq_neg_one hM_mul_cM_sq
  refine ⟨D.d g, ⟨g, rfl⟩, ?_⟩
  have hgc : g⁻¹ * hM * g = hM * cM := by
    have h := congrArg (fun x => g⁻¹ * x * g) hg
    rw [show g⁻¹ * (g * (hM * cM) * g⁻¹) * g = hM * cM by group] at h
    exact h.symm
  calc (D.d g)⁻¹ * D.v * D.d g = (D.d g)⁻¹ * D.d hM * D.d g := rfl
    _ = D.d (g⁻¹ * hM * g) := by rw [map_mul, map_mul, map_inv]
    _ = D.d (hM * cM) := by rw [hgc]
    _ = D.v * D.w := by rw [map_mul]; rfl

theorem commutator_A_eq : (commutator D.A).map D.A.subtype = D.A := by
  obtain ⟨e⟩ := D.nonempty_A_mulEquiv_alt5
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (α := Fin 5) (by simp))
  haveI : Group.IsPerfect D.A :=
    Group.IsPerfect.ofSurjective (f := (e.symm : alternatingGroup (Fin 5) →* D.A))
      (MulEquiv.surjective e.symm)
  exact (Subgroup.map_subtype_commutator D.A).trans Subgroup.commutator_eq_self

end SwapData

namespace SplitData

variable {G : Type} [Group G] (D : SplitData G)

theorem isConj_u_of_mem {x : G} (hx : x = D.v ∨ x = D.w ∨ x = D.v * D.w) : IsConj D.u x := by
  have hvw : IsConj D.v D.w := by
    obtain ⟨g, -, hg⟩ := D.exists_mem_A_conj_v_eq_w
    exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩
  have hvww : IsConj D.v (D.v * D.w) := by
    obtain ⟨g, -, hg⟩ := D.exists_mem_A_conj_v_eq_v_mul_w
    exact isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hg⟩
  rcases hx with rfl | rfl | rfl
  · exact D.isConj_u_v
  · exact D.isConj_u_v.trans hvw
  · exact D.isConj_u_v.trans hvww

theorem isConj_t_u_mul {x : G} (hx : x = D.v ∨ x = D.w ∨ x = D.v * D.w) :
    IsConj D.t (D.u * x) := by
  have huv : IsConj D.t (D.u * D.v) :=
    isConj_iff.mpr ⟨D.z⁻¹, by rw [inv_inv]; exact D.z_t⟩
  have huw : IsConj (D.u * D.v) (D.u * D.w) := by
    obtain ⟨g, hgA, hg⟩ := D.exists_mem_A_conj_v_eq_w
    obtain ⟨y, rfl⟩ := hgA
    have hgu : (D.d y)⁻¹ * D.u * D.d y = D.u := by
      rw [mul_assoc, ← (D.d_commute_u y).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    refine isConj_iff.mpr ⟨(D.d y)⁻¹, ?_⟩
    rw [inv_inv]
    calc (D.d y)⁻¹ * (D.u * D.v) * D.d y
        = ((D.d y)⁻¹ * D.u * D.d y) * ((D.d y)⁻¹ * D.v * D.d y) := by group
      _ = D.u * D.w := by rw [hgu, hg]
  have huww : IsConj (D.u * D.v) (D.u * (D.v * D.w)) := by
    obtain ⟨g, hgA, hg⟩ := D.exists_mem_A_conj_v_eq_v_mul_w
    obtain ⟨y, rfl⟩ := hgA
    have hgu : (D.d y)⁻¹ * D.u * D.d y = D.u := by
      rw [mul_assoc, ← (D.d_commute_u y).eq, ← mul_assoc, inv_mul_cancel, one_mul]
    refine isConj_iff.mpr ⟨(D.d y)⁻¹, ?_⟩
    rw [inv_inv]
    calc (D.d y)⁻¹ * (D.u * D.v) * D.d y
        = ((D.d y)⁻¹ * D.u * D.d y) * ((D.d y)⁻¹ * D.v * D.d y) := by group
      _ = D.u * (D.v * D.w) := by rw [hgu, hg]
  rcases hx with rfl | rfl | rfl
  · exact huv
  · exact huv.trans huw
  · exact huv.trans huww

end SplitData

end CFSG.OddTranspositions.PartThree.Wong
