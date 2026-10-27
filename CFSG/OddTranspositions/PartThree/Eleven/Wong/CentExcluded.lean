module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentTransferData
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentClasses

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem transfer_excluded_involutions :
    orderOf D.r = 2 ∧ orderOf (D.r * D.a * D.w) = 2 ∧
    (∀ g ∈ D.X, g⁻¹ * D.r * g ∉ D.M) ∧ ∀ g ∈ D.X, g⁻¹ * (D.r * D.a * D.w) * g ∉ D.M := by
  have hr_ne_one : D.r ≠ 1 := by
    intro h
    change D.t * D.u = 1 at h
    have hu : D.u = D.t := by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right D.t_mul_t]
    exact D.u_not_mem (hu ▸ D.t_mem_K)
  have hr_order : orderOf D.r = 2 := orderOf_eq_prime D.r_sq hr_ne_one
  obtain ⟨-, -, -, -, -, -, -, hinvM, -, -⟩ := D.transfer_subgroup_data
  obtain ⟨m, hm⟩ := D.fusion_element_w_action
  have har : D.a * D.r = D.r * D.b := by
    have h := D.conj_r_a_and_b.1
    calc D.a * D.r = D.r * (D.r⁻¹ * D.a * D.r) := by group
      _ = D.r * D.b := by rw [h]
  have hwa : D.w * D.a = D.b⁻¹ * D.w := by
    have h := D.conj_w_a_and_b.1
    rw [inv_eq_of_mul_eq_one_right D.w_mul_w] at h
    calc D.w * D.a = D.w * D.a * (D.w * D.w) := by rw [D.w_mul_w, mul_one]
      _ = (D.w * D.a * D.w) * D.w := by group
      _ = D.b⁻¹ * D.w := by rw [h]
  have hraw_sq : (D.r * D.a * D.w) ^ 2 = 1 := by
    rw [pow_two]
    calc D.r * D.a * D.w * (D.r * D.a * D.w)
        = D.r * D.a * (D.w * D.r) * D.a * D.w := by group
      _ = D.r * D.a * (D.r * D.w) * D.a * D.w := by rw [D.commute_w_r.eq]
      _ = D.r * (D.a * D.r) * D.w * D.a * D.w := by group
      _ = D.r * (D.r * D.b) * D.w * D.a * D.w := by rw [har]
      _ = D.r * D.r * D.b * D.w * D.a * D.w := by group
      _ = D.b * D.w * D.a * D.w := by rw [← pow_two, D.r_sq, one_mul]
      _ = D.b * (D.w * D.a) * D.w := by group
      _ = D.b * (D.b⁻¹ * D.w) * D.w := by rw [hwa]
      _ = 1 := by
            rw [show D.b * (D.b⁻¹ * D.w) * D.w = (D.b * D.b⁻¹) * (D.w * D.w) by group,
              mul_inv_cancel, D.w_mul_w, mul_one]
  have hraw_not_M : D.r * D.a * D.w ∉ D.M := by
    intro h
    apply D.r_not_mem_M
    have haw : D.a * D.w ∈ D.M :=
      mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    have h' := mul_mem h (inv_mem haw)
    rwa [show (D.r * D.a * D.w) * (D.a * D.w)⁻¹ = D.r by group] at h'
  have hraw_ne_one : D.r * D.a * D.w ≠ 1 :=
    fun h => hraw_not_M (by rw [h]; exact one_mem D.M)
  have hraw_order : orderOf (D.r * D.a * D.w) = 2 := orderOf_eq_prime hraw_sq hraw_ne_one
  have hu_comm_raw : Commute D.u (D.r * D.a * D.w) := by
    have hr : Commute D.u D.r := D.t_commute_u.symm.mul_right (Commute.refl D.u)
    have ha : Commute D.u D.a :=
      (mem_centralizer_singleton_iff.mp (D.T_le_X D.a_mem_T)).symm
    have hw : Commute D.u D.w :=
      (mem_centralizer_singleton_iff.mp (D.T_le_X D.w_mem_T)).symm
    exact (hr.mul_right ha).mul_right hw
  have huraw_sq : (D.u * (D.r * D.a * D.w)) ^ 2 = 1 := by
    rw [hu_comm_raw.mul_pow, show D.u ^ 2 = 1 by rw [pow_two, D.u_mul_u], hraw_sq, one_mul]
  have huraw_ne_one : D.u * (D.r * D.a * D.w) ≠ 1 := by
    intro h
    have : D.r * D.a * D.w = D.u := by
      calc D.r * D.a * D.w = D.u⁻¹ * (D.u * (D.r * D.a * D.w)) := by group
        _ = D.u⁻¹ * 1 := by rw [h]
        _ = D.u := by rw [mul_one, D.u_inv]
    exact hraw_not_M (by rw [this]; exact D.u_mem_M)
  have huraw_order : orderOf (D.u * (D.r * D.a * D.w)) = 2 :=
    orderOf_eq_prime huraw_sq huraw_ne_one
  have hzw : D.z * D.w * D.z⁻¹ = D.t * D.u * D.v ^ m.val * D.w := by
    have hφ : D.z⁻¹ * (D.t * D.u * D.v ^ m.val * D.w) * D.z = D.w := by
      have h : D.z⁻¹ * (D.t * D.u * D.v ^ m.val * D.w) * D.z =
          D.z⁻¹ * D.t * D.z * (D.z⁻¹ * D.u * D.z) * (D.z⁻¹ * D.v * D.z) ^ m.val *
            (D.z⁻¹ * D.w * D.z) := by
        rw [show (D.z⁻¹ * D.v * D.z) ^ m.val = D.z⁻¹ * D.v ^ m.val * D.z by
          rw [show D.z⁻¹ * D.v * D.z = (MulAut.conj D.z⁻¹) D.v by
                rw [MulAut.conj_apply, inv_inv],
            ← map_pow (MulAut.conj D.z⁻¹) D.v m, MulAut.conj_apply, inv_inv]]
        group
      rw [h, D.z_t', D.z_u', D.z_v', hm]
      fin_cases m <;>
        simp only [pow_zero, pow_one, mul_one, mul_assoc, D.v_mul_t_mul, D.u_mul_t_mul,
          D.t_mul_t_mul, D.v_mul_u_mul, D.u_mul_u_mul, D.v_mul_v_mul]
    calc D.z * D.w * D.z⁻¹
        = D.z * (D.z⁻¹ * (D.t * D.u * D.v ^ m.val * D.w) * D.z) * D.z⁻¹ := by rw [hφ]
      _ = D.t * D.u * D.v ^ m.val * D.w := by group
  have hzu : D.z * D.u * D.z⁻¹ = D.t * D.v := by
    have hφ : D.z⁻¹ * (D.t * D.v) * D.z = D.u := by
      calc D.z⁻¹ * (D.t * D.v) * D.z
          = (D.z⁻¹ * D.t * D.z) * (D.z⁻¹ * D.v * D.z) := by group
        _ = D.u := by rw [D.z_t', D.z_v', mul_assoc, D.v_mul_v, mul_one]
    calc D.z * D.u * D.z⁻¹
        = D.z * (D.z⁻¹ * (D.t * D.v) * D.z) * D.z⁻¹ := by rw [hφ]
      _ = D.t * D.v := by group
  have hzraw : D.z * (D.r * D.a * D.w) * D.z⁻¹ = D.h2 * D.v ^ m.val * D.w := by
    have hzr : D.z * D.r * D.z⁻¹ = D.r := by
      calc D.z * D.r * D.z⁻¹ = D.z * (D.z⁻¹ * D.r * D.z) * D.z⁻¹ := by rw [D.z_conj_r]
        _ = D.r := by group
    have hza : D.z * D.a * D.z⁻¹ = D.h1 := by
      rw [show D.a = D.z⁻¹ * D.h1 * D.z from rfl]; group
    calc D.z * (D.r * D.a * D.w) * D.z⁻¹
        = (D.z * D.r * D.z⁻¹) * (D.z * D.a * D.z⁻¹) * (D.z * D.w * D.z⁻¹) := by group
      _ = D.r * D.h1 * (D.t * D.u * D.v ^ m.val * D.w) := by rw [hzr, hza, hzw]
      _ = D.h2 * D.v ^ m.val * D.w := by
          have h1 : D.r * D.h1 = D.t * (D.h2 * D.u) := by
            rw [show D.r = D.t * D.u from rfl, mul_assoc,
              show D.u * D.h1 = D.h2 * D.u from D.u_mul_i1 hM]
          have h2 : D.t * (D.h2 * D.u) = D.h2 * D.t * D.u := by
            rw [← mul_assoc, show D.t * D.h2 = D.h2 * D.t from (D.t_commute_i2 hM).eq]
          rw [h1, h2]
          simp only [mul_assoc]
          rw [D.u_mul_t_mul, D.u_mul_u_mul, D.t_mul_t_mul]
  have hzuraw : D.z * (D.u * (D.r * D.a * D.w)) * D.z⁻¹ =
      D.t * D.v * (D.h2 * D.v ^ m.val * D.w) := by
    calc D.z * (D.u * (D.r * D.a * D.w)) * D.z⁻¹
        = (D.z * D.u * D.z⁻¹) * (D.z * (D.r * D.a * D.w) * D.z⁻¹) := by group
      _ = D.t * D.v * (D.h2 * D.v ^ m.val * D.w) := by rw [hzu, hzraw]
  have hord1 : orderOf (D.h2 * D.v ^ m.val * D.w) = 2 := by
    have h : D.h2 * D.v ^ m.val * D.w = (MulAut.conj D.z).toMonoidHom
        (D.r * D.a * D.w) := by
      change D.h2 * D.v ^ m.val * D.w = (MulAut.conj D.z) (D.r * D.a * D.w)
      rw [MulAut.conj_apply]; exact hzraw.symm
    rw [h, orderOf_injective (MulAut.conj D.z).toMonoidHom (MulAut.conj D.z).injective
      (D.r * D.a * D.w), hraw_order]
  have hord2 : orderOf (D.t * D.v * (D.h2 * D.v ^ m.val * D.w)) = 2 := by
    have h : D.t * D.v * (D.h2 * D.v ^ m.val * D.w) = (MulAut.conj D.z).toMonoidHom
        (D.u * (D.r * D.a * D.w)) := by
      change D.t * D.v * (D.h2 * D.v ^ m.val * D.w) =
        (MulAut.conj D.z) (D.u * (D.r * D.a * D.w))
      rw [MulAut.conj_apply]; exact hzuraw.symm
    rw [h, orderOf_injective (MulAut.conj D.z).toMonoidHom (MulAut.conj D.z).injective
      (D.u * (D.r * D.a * D.w)), huraw_order]
  have hu_conj_h2 : D.u * D.h2 * D.u = D.h1 := by
    have h := D.u_conj_i2 hM
    rw [D.u_inv] at h
    exact h
  have hu_conj_v : D.u * D.v * D.u = D.v := by
    have h := D.u_conj_prod hM hM
    rw [D.u_inv] at h
    exact h
  have hu_conj_w : D.u * D.w * D.u = D.w := by
    have h := D.u_conj_prod cM cM
    rw [D.u_inv] at h
    exact h
  have hcu : (MulAut.conj D.u) (D.h2 * D.v ^ m.val * D.w) = D.h1 * D.v ^ m.val * D.w := by
    rw [map_mul, map_mul, map_pow]
    rw [show (MulAut.conj D.u) D.h2 = D.h1 by
          rw [MulAut.conj_apply, D.u_inv]; exact hu_conj_h2,
        show (MulAut.conj D.u) D.v = D.v by
          rw [MulAut.conj_apply, D.u_inv]; exact hu_conj_v,
        show (MulAut.conj D.u) D.w = D.w by
          rw [MulAut.conj_apply, D.u_inv]; exact hu_conj_w]
  have hut : (MulAut.conj D.u) D.t = D.t := by
    rw [MulAut.conj_apply, D.u_inv, ← D.t_commute_u.eq, mul_assoc, D.u_mul_u, mul_one]
  have hne1 : D.h2 * D.v ^ m.val * D.w ≠ D.t := by
    intro h
    have heq : D.h1 * D.v ^ m.val * D.w = D.h2 * D.v ^ m.val * D.w := by
      rw [← hcu, h, hut, ← h]
    have h12 : D.h1 = D.h2 := by
      rw [mul_assoc, mul_assoc] at heq
      exact mul_right_cancel heq
    exact D.t_ne_d hM (by
      rw [show D.d hM = D.h1 * D.h2 from rfl, h12, ← pow_two, D.h2_sq])
  have hu_tv : (MulAut.conj D.u) (D.t * D.v) = D.t * D.v := by
    rw [map_mul, hut, show (MulAut.conj D.u) D.v = D.v by
      rw [MulAut.conj_apply, D.u_inv]; exact hu_conj_v]
  have hcu2 : (MulAut.conj D.u) ((D.t * D.v) * (D.h2 * D.v ^ m.val * D.w)) =
      (D.t * D.v) * (D.h1 * D.v ^ m.val * D.w) := by
    rw [map_mul, hu_tv, hcu]
  have hne2 : D.t * D.v * (D.h2 * D.v ^ m.val * D.w) ≠ D.t := by
    intro h
    have heq : (D.t * D.v) * (D.h1 * D.v ^ m.val * D.w) =
        (D.t * D.v) * (D.h2 * D.v ^ m.val * D.w) := by
      rw [← hcu2, h, hut, ← h]
    have h12 : D.h1 = D.h2 := by
      have heq' := mul_left_cancel (a := D.t * D.v) heq
      rw [mul_assoc, mul_assoc] at heq'
      exact mul_right_cancel heq'
    exact D.t_ne_d hM (by
      rw [show D.d hM = D.h1 * D.h2 from rfl, h12, ← pow_two, D.h2_sq])
  have hh2K : D.h2 ∈ D.K := D.mem_K_iff.mpr ⟨1, hM, by rw [map_one, one_mul]; rfl⟩
  have hvK : D.v ∈ D.K := D.d_mem_K hM
  have hwK : D.w ∈ D.K := D.d_mem_K cM
  have htK : D.t ∈ D.K := D.t_mem_K
  have hK1 : D.h2 * D.v ^ m.val * D.w ∈ D.K :=
    mul_mem (mul_mem hh2K (pow_mem hvK _)) hwK
  have hK2 : D.t * D.v * (D.h2 * D.v ^ m.val * D.w) ∈ D.K :=
    mul_mem (mul_mem htK hvK) hK1
  have hconj1 : IsConj D.u (D.h2 * D.v ^ m.val * D.w) := by
    have hv1 : IsConj D.v (D.h2 * D.v ^ m.val * D.w) := by
      obtain ⟨k, -, hk⟩ := D.exists_conj_v_of_mem_K hK1 hord1 hne1
      exact isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩
    exact D.isConj_u_v.trans hv1
  have hconj2 : IsConj D.u (D.t * D.v * (D.h2 * D.v ^ m.val * D.w)) := by
    have hv2 : IsConj D.v (D.t * D.v * (D.h2 * D.v ^ m.val * D.w)) := by
      obtain ⟨k, -, hk⟩ := D.exists_conj_v_of_mem_K hK2 hord2 hne2
      exact isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩
    exact D.isConj_u_v.trans hv2
  have huraw_conj : IsConj D.u (D.r * D.a * D.w) := by
    have h : IsConj (D.h2 * D.v ^ m.val * D.w) (D.r * D.a * D.w) := by
      refine isConj_iff.mpr ⟨D.z⁻¹, ?_⟩
      rw [inv_inv, ← hzraw]
      group
    exact hconj1.trans h
  have hu_uraw : IsConj D.u (D.u * (D.r * D.a * D.w)) := by
    have h : IsConj (D.t * D.v * (D.h2 * D.v ^ m.val * D.w))
        (D.u * (D.r * D.a * D.w)) := by
      refine isConj_iff.mpr ⟨D.z⁻¹, ?_⟩
      rw [inv_inv, ← hzuraw]
      group
    exact hconj2.trans h
  have hgu : ∀ g ∈ D.X, g⁻¹ * D.u * g = D.u := by
    intro g hg
    have h := mem_centralizer_singleton_iff.mp hg
    rw [mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]
  have hr_not_conj : ∀ g ∈ D.X, g⁻¹ * D.r * g ∉ D.M := by
    intro g hg hgM
    have hgu' := hgu g hg
    set x := g⁻¹ * D.r * g with hx
    have hxM : x ∈ D.M := hgM
    have hx2 : orderOf x = 2 := by
      have hxconj : x = (MulAut.conj g⁻¹).toMonoidHom D.r := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hx
      rw [hxconj, orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective D.r, hr_order]
    have htx : IsConj D.t x := by
      refine D.isConj_t_tu.trans ?_
      refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
      rw [inv_inv, show D.t * D.u = D.r from rfl]
    have hur : D.u * D.r = D.t := by
      rw [show D.r = D.t * D.u from rfl, D.u_mul_t_mul, D.u_mul_u, mul_one]
    rcases (hinvM x hxM).mp hx2 with h | h | h | h | h | h | h
    · exact D.not_isConj_t_u (h ▸ htx)
    · exact D.not_isConj_t_u
        (htx.trans (h.symm ▸ D.isConj_u_of_mem (x := D.v) (Or.inl rfl)).symm)
    · exact D.not_isConj_t_u
        (htx.trans (h.symm ▸ D.isConj_u_of_mem (x := D.w) (Or.inr (Or.inl rfl))).symm)
    · exact D.not_isConj_t_u
        (htx.trans (h.symm ▸ D.isConj_u_of_mem (x := D.v * D.w)
          (Or.inr (Or.inr rfl))).symm)
    · have hty : IsConj D.t D.v := by
        have hux : IsConj D.t (D.u * x) := by
          have h : g⁻¹ * D.t * g = D.u * x := by
            calc g⁻¹ * D.t * g = g⁻¹ * (D.u * D.r) * g := by rw [← hur]
              _ = (g⁻¹ * D.u * g) * (g⁻¹ * D.r * g) := by group
              _ = D.u * x := by rw [hgu', ← hx]
          refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
          simpa only [inv_inv] using h
        rwa [h, D.u_mul_u_mul] at hux
      exact D.not_isConj_t_u
        (hty.trans (D.isConj_u_of_mem (x := D.v) (Or.inl rfl)).symm)
    · have hty : IsConj D.t D.w := by
        have hux : IsConj D.t (D.u * x) := by
          have h : g⁻¹ * D.t * g = D.u * x := by
            calc g⁻¹ * D.t * g = g⁻¹ * (D.u * D.r) * g := by rw [← hur]
              _ = (g⁻¹ * D.u * g) * (g⁻¹ * D.r * g) := by group
              _ = D.u * x := by rw [hgu', ← hx]
          refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
          simpa only [inv_inv] using h
        rwa [h, D.u_mul_u_mul] at hux
      exact D.not_isConj_t_u
        (hty.trans (D.isConj_u_of_mem (x := D.w) (Or.inr (Or.inl rfl))).symm)
    · have hty : IsConj D.t (D.v * D.w) := by
        have hux : IsConj D.t (D.u * x) := by
          have h : g⁻¹ * D.t * g = D.u * x := by
            calc g⁻¹ * D.t * g = g⁻¹ * (D.u * D.r) * g := by rw [← hur]
              _ = (g⁻¹ * D.u * g) * (g⁻¹ * D.r * g) := by group
              _ = D.u * x := by rw [hgu', ← hx]
          refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
          simpa only [inv_inv] using h
        rw [h] at hux
        rw [← mul_assoc, D.u_mul_u_mul] at hux
        exact hux
      exact D.not_isConj_t_u
        (hty.trans (D.isConj_u_of_mem (x := D.v * D.w) (Or.inr (Or.inr rfl))).symm)
  have hraw_not_conj : ∀ g ∈ D.X, g⁻¹ * (D.r * D.a * D.w) * g ∉ D.M := by
    intro g hg hgM
    have hgu' := hgu g hg
    set x := g⁻¹ * (D.r * D.a * D.w) * g with hx
    have hxM : x ∈ D.M := hgM
    have hx2 : orderOf x = 2 := by
      have hxconj : x = (MulAut.conj g⁻¹).toMonoidHom (D.r * D.a * D.w) := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hx
      rw [hxconj, orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective (D.r * D.a * D.w), hraw_order]
    have hrawx : IsConj (D.r * D.a * D.w) x := by
      refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
      simpa only [inv_inv] using hx.symm
    have hux : IsConj (D.u * (D.r * D.a * D.w)) (D.u * x) := by
      refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
      simpa only [inv_inv] using
        (show g⁻¹ * (D.u * (D.r * D.a * D.w)) * g = D.u * x by
          calc g⁻¹ * (D.u * (D.r * D.a * D.w)) * g
              = (g⁻¹ * D.u * g) * (g⁻¹ * (D.r * D.a * D.w) * g) := by group
            _ = D.u * x := by rw [hgu', ← hx])
    rcases (hinvM x hxM).mp hx2 with h | h | h | h | h | h | h
    · have hraw_u : D.r * D.a * D.w = D.u := by
        have h1 : g⁻¹ * (D.r * D.a * D.w) * g = D.u := hx.symm.trans h
        calc D.r * D.a * D.w = g * (g⁻¹ * (D.r * D.a * D.w) * g) * g⁻¹ := by group
          _ = g * D.u * g⁻¹ := by rw [h1]
          _ = D.u := by
              conv_lhs => rw [← hgu']
              group
      exact hraw_not_M (by rw [hraw_u]; exact D.u_mem_M)
    · exact D.not_isConj_t_u
        ((h.symm ▸ D.isConj_t_u_mul (x := D.v) (Or.inl rfl)).trans
          (hu_uraw.trans hux).symm)
    · exact D.not_isConj_t_u
        ((h.symm ▸ D.isConj_t_u_mul (x := D.w) (Or.inr (Or.inl rfl))).trans
          (hu_uraw.trans hux).symm)
    · exact D.not_isConj_t_u
        ((h.symm ▸ D.isConj_t_u_mul (x := D.v * D.w) (Or.inr (Or.inr rfl))).trans
          (hu_uraw.trans hux).symm)
    · have htx : IsConj D.t x := h.symm ▸ D.isConj_t_u_mul (x := D.v) (Or.inl rfl)
      have hux' : IsConj D.u x := huraw_conj.trans hrawx
      exact D.not_isConj_t_u (htx.trans hux'.symm)
    · have htx : IsConj D.t x := h.symm ▸ D.isConj_t_u_mul (x := D.w) (Or.inr (Or.inl rfl))
      have hux' : IsConj D.u x := huraw_conj.trans hrawx
      exact D.not_isConj_t_u (htx.trans hux'.symm)
    · have htx : IsConj D.t x := h.symm ▸
        (show IsConj D.t (D.u * D.v * D.w) from by
          rw [show D.u * D.v * D.w = D.u * (D.v * D.w) by rw [mul_assoc]]
          exact D.isConj_t_u_mul (x := D.v * D.w) (Or.inr (Or.inr rfl)))
      have hux' : IsConj D.u x := huraw_conj.trans hrawx
      exact D.not_isConj_t_u (htx.trans hux'.symm)
  exact ⟨hr_order, hraw_order, hr_not_conj, hraw_not_conj⟩

end CFSG.OddTranspositions.PartThree.Wong.SplitData
