module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentFusion

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup

variable {G : Type} [Group G] (D : SplitData G)

private theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a

private theorem commute_conj_z {a b : G} (h : Commute a b) :
    Commute (D.z⁻¹ * a * D.z) (D.z⁻¹ * b * D.z) :=
  calc D.z⁻¹ * a * D.z * (D.z⁻¹ * b * D.z) = D.z⁻¹ * (a * b) * D.z := by group
    _ = D.z⁻¹ * (b * a) * D.z := by rw [h.eq]
    _ = D.z⁻¹ * b * D.z * (D.z⁻¹ * a * D.z) := by group

theorem z_t' : D.z⁻¹ * D.t * D.z = D.u * D.v := D.z_t
theorem z_u' : D.z⁻¹ * D.u * D.z = D.t * D.v := D.z_u
theorem z_v' : D.z⁻¹ * D.v * D.z = D.v := D.z_v

theorem z_conj_r : D.z⁻¹ * D.r * D.z = D.r := by
  have h : D.z⁻¹ * D.r * D.z = D.z⁻¹ * D.t * D.z * (D.z⁻¹ * D.u * D.z) := by
    rw [show D.r = D.t * D.u from rfl]
    group
  rw [h, D.z_t', D.z_u', show D.r = D.t * D.u from rfl]
  simp only [mul_assoc, D.v_mul_t_mul, D.v_mul_v, mul_one, D.u_mul_t]

theorem z_conj_w_mem_E [Finite G] : D.z⁻¹ * D.w * D.z ∈ D.E := by
  have h1 := D.commute_conj_z D.commute_t_w
  have h2 := D.commute_conj_z D.commute_u_w
  have h3 := D.commute_conj_z D.commute_v_w
  rw [D.z_t'] at h1
  rw [D.z_u'] at h2
  rw [D.z_v'] at h3
  have ht : Commute D.t (D.z⁻¹ * D.w * D.z) := by
    simpa only [mul_assoc, D.v_mul_v, mul_one] using h2.mul_left h3
  have hu : Commute D.u (D.z⁻¹ * D.w * D.z) := by
    simpa only [mul_assoc, D.v_mul_v, mul_one] using h1.mul_left h3
  rw [← D.centralizer_t_u_v]
  refine mem_centralizer_iff.mpr ?_
  rintro _ (rfl | rfl | rfl)
  exacts [ht.eq, hu.eq, h3.eq]

theorem fusion_element_w_action [Finite G] :
    ∃ m : Fin 2, D.z⁻¹ * D.w * D.z = D.t * D.u * D.v ^ m.val * D.w := by
  set y := D.z⁻¹ * D.w * D.z with hy
  have hyE : y ∈ D.E := D.z_conj_w_mem_E
  have htvy : D.t * D.v * y = D.z⁻¹ * (D.u * D.w) * D.z := by
    rw [hy, show D.z⁻¹ * (D.u * D.w) * D.z = D.z⁻¹ * D.u * D.z * (D.z⁻¹ * D.w * D.z) by group,
      D.z_u']
  have hconj : IsConj D.t (D.t * D.v * y) := by
    rw [htvy]
    exact (D.isConj_t_u_mul_d cM_sq).trans (isConj_iff.mpr ⟨D.z⁻¹, by rw [inv_inv]; rfl⟩)
  have hmem : D.t * D.v * y ∈ D.E :=
    mul_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) hyE
  have hy' : y = D.v * (D.t * (D.t * D.v * y)) := by
    simp only [mul_assoc, D.t_mul_t_mul, D.v_mul_v_mul]
  have hinj : ∀ a b : G, D.z⁻¹ * a * D.z = D.z⁻¹ * b * D.z → a = b := fun a b h => by
    simpa using h
  rcases (D.isConj_t_iff_of_mem_E hmem (by rw [orderOf_eq_of_isConj hconj, D.orderOf_t])).mp
    hconj with h | h | h | h | h <;> rw [h] at hy'
  · simp only [D.t_mul_t, mul_one] at hy'
    exact absurd (hinj _ _ (hy.symm.trans (hy'.trans D.z_v'.symm))) D.w_ne_v
  · simp only [D.t_mul_t_mul, D.v_mul_u] at hy'
    exact absurd (hinj _ _ (hy.symm.trans (hy'.trans D.z_t'.symm)))
      (fun h => D.t_ne_d cM h.symm)
  · simp only [D.v_mul_t_mul, D.v_mul_u_mul, D.v_mul_v, mul_one] at hy'
    refine absurd (hinj _ _ (hy.symm.trans (hy'.trans D.z_conj_r.symm))) fun h => ?_
    exact D.t_mul_u_not_mem_K (by rw [show D.t * D.u = D.w from h.symm]; exact D.d_mem_K cM)
  · refine ⟨1, hy'.trans ?_⟩
    simp only [Fin.val_one, pow_one, mul_assoc, D.v_mul_t_mul, D.v_mul_u_mul]
  · refine ⟨0, hy'.trans ?_⟩
    simp only [Fin.val_zero, pow_zero, mul_one, mul_assoc, D.v_mul_t_mul, D.v_mul_u_mul,
      D.v_mul_v_mul]

end CFSG.OddTranspositions.PartThree.Wong.SplitData
