module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentT

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem normalized_y_equations {s : G} (hs2 : s ^ 2 = D.u) (hst : D.t⁻¹ * s * D.t = s⁻¹)
    (hψ : ∀ x x' : SL5, psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM → s⁻¹ * D.d x * s = D.d x') :
    s * D.w ∈ normalizer (D.D1 : Set G) ∧
    (s * D.w)⁻¹ * D.v * (s * D.w) = D.v ∧ (s * D.w)⁻¹ * D.w * (s * D.w) = D.v * D.w ∧
    (s * D.w) ^ 2 = D.u * D.v ∧
    (s * D.w)⁻¹ * D.t * (s * D.w) = D.t * D.u ∧
    (s * D.w)⁻¹ * (D.t * D.u) * (s * D.w) = D.t ∧
    ∀ q : ZMod 5, (s * D.w)⁻¹ * D.d (thetaM q) * (s * D.w) = D.d (thetaM (3 * q)) := by
  have hs2' : s * s = D.u := by rw [← pow_two, hs2]
  have hchar : ∀ q : ZMod 5, -(2 * q) = 3 * q := by decide
  have h32 : ∀ q : ZMod 5, (3 : ZMod 5) * (2 * q) = q := by decide
  have hcminv : cM⁻¹ = -cM :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← pow_two, cM_sq, neg_neg])
  have hsv : s⁻¹ * D.v * s = D.v := by
    have hmat : psiM * ((hM⁻¹ : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
        (hM : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := by decide
    have h := hψ hM hM⁻¹ hmat
    have hd : D.d hM⁻¹ = D.v := by
      rw [map_inv, ← D.v_eq_d, inv_eq_of_mul_eq_one_right D.v_mul_v]
    exact (show s⁻¹ * D.v * s = D.d hM⁻¹ from h).trans hd
  have hsw : s⁻¹ * D.w * s = D.v * D.w := by
    have hmat : psiM * (((-(hM * cM)) : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
        (cM : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := by decide
    have h := hψ cM (-(hM * cM)) hmat
    have hd : D.d (-(hM * cM)) = D.v * D.w := by
      rw [D.d_neg, map_mul, ← D.v_eq_d, ← D.w_eq_d]
    exact (show s⁻¹ * D.w * s = D.d (-(hM * cM)) from h).trans hd
  have hwt : D.w⁻¹ * D.t * D.w = D.t := by
    rw [mul_assoc, D.commute_t_w.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwu : D.w⁻¹ * D.u * D.w = D.u := by
    rw [mul_assoc, D.commute_u_w.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwv : D.w⁻¹ * D.v * D.w = D.v := by
    rw [mul_assoc, D.commute_v_w.eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hsts : s⁻¹ * D.t * s = D.u * D.t := by
    have hst2 : D.t * s * D.t = s⁻¹ := by simpa [D.t_inv] using hst
    have h : s⁻¹ * D.t * s * D.t = D.u := by
      calc s⁻¹ * D.t * s * D.t = s⁻¹ * (D.t * s * D.t) := by group
        _ = s⁻¹ * s⁻¹ := by rw [hst2]
        _ = D.u := by rw [← mul_inv_rev, ← pow_two, hs2, D.u_inv]
    calc s⁻¹ * D.t * s = (s⁻¹ * D.t * s) * (D.t * D.t) := by rw [D.t_mul_t, mul_one]
      _ = ((s⁻¹ * D.t * s) * D.t) * D.t := by group
      _ = D.u * D.t := by rw [h]
  have hus : s⁻¹ * D.u * s = D.u := by
    rw [← hs2']
    group
  have hconj : ∀ q : ZMod 5,
      (s * D.w)⁻¹ * D.d (thetaM q) * (s * D.w) = D.d (thetaM (3 * q)) := by
    intro q
    let xp : SL5 := ⟨!![1, (2 : ZMod 5) * q; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hxp : (xp : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
        !![1, (2 : ZMod 5) * q; 0, 1] := rfl
    have hmat : psiM * (xp : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
        (thetaM q : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := by
      rw [hxp]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [psiM, thetaM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have h := hψ (thetaM q) xp hmat
    have hcx : cM⁻¹ * xp * cM = thetaM (3 * q) := by
      apply Subtype.ext
      rw [hcminv]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, hxp,
        Matrix.SpecialLinearGroup.coe_mk]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [cM, thetaM, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | rfl | exact hchar q
    calc (s * D.w)⁻¹ * D.d (thetaM q) * (s * D.w)
        = D.w⁻¹ * (s⁻¹ * D.d (thetaM q) * s) * D.w := by group
      _ = D.w⁻¹ * D.d xp * D.w := by rw [h]
      _ = D.d (cM⁻¹ * xp * cM) := by
          change (D.d cM)⁻¹ * D.d xp * D.d cM = D.d (cM⁻¹ * xp * cM)
          rw [← map_inv, ← map_mul, ← map_mul]
      _ = D.d (thetaM (3 * q)) := by rw [hcx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hconj⟩
  · refine mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [show D.D1 = closure (Set.range (fun q : ZMod 5 => D.d (thetaM q))) from rfl,
      MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    ext g
    constructor
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      refine ⟨2 * q, ?_⟩
      have hq := hconj (2 * q)
      rw [h32 q] at hq
      show D.d (thetaM (2 * q)) = (s * D.w) * D.d (thetaM q) * (s * D.w)⁻¹
      calc D.d (thetaM (2 * q))
          = (s * D.w) * ((s * D.w)⁻¹ * D.d (thetaM (2 * q)) * (s * D.w)) *
              (s * D.w)⁻¹ := by group
        _ = (s * D.w) * D.d (thetaM q) * (s * D.w)⁻¹ := by rw [hq]
    · rintro ⟨q, rfl⟩
      refine ⟨D.d (thetaM (3 * q)), ⟨3 * q, rfl⟩, ?_⟩
      have hq := hconj q
      show (s * D.w) * D.d (thetaM (3 * q)) * (s * D.w)⁻¹ = D.d (thetaM q)
      calc (s * D.w) * D.d (thetaM (3 * q)) * (s * D.w)⁻¹
          = (s * D.w) * ((s * D.w)⁻¹ * D.d (thetaM q) * (s * D.w)) *
              (s * D.w)⁻¹ := by rw [← hq]
        _ = D.d (thetaM q) := by group
  · calc (s * D.w)⁻¹ * D.v * (s * D.w)
        = D.w⁻¹ * (s⁻¹ * D.v * s) * D.w := by group
      _ = D.w⁻¹ * D.v * D.w := by rw [hsv]
      _ = D.v := hwv
  · calc (s * D.w)⁻¹ * D.w * (s * D.w)
        = D.w⁻¹ * (s⁻¹ * D.w * s) * D.w := by group
      _ = D.w⁻¹ * (D.v * D.w) * D.w := by rw [hsw]
      _ = D.v * D.w := by
          simp only [mul_assoc, D.w_mul_w, mul_one]
          rw [inv_eq_of_mul_eq_one_right D.w_mul_w, D.w_mul_v]
  · have hws : D.w * s = s * (D.v * D.w) := by
      calc D.w * s = s * (s⁻¹ * D.w * s) := by group
        _ = s * (D.v * D.w) := by rw [hsw]
    calc (s * D.w) ^ 2 = s * D.w * (s * D.w) := by rw [pow_two]
      _ = s * (D.w * s) * D.w := by group
      _ = s * (s * (D.v * D.w)) * D.w := by rw [hws]
      _ = (s * s) * (D.v * D.w) * D.w := by group
      _ = D.u * D.v := by
          rw [← pow_two, hs2]
          simp only [mul_assoc, D.w_mul_w, mul_one]
  · calc (s * D.w)⁻¹ * D.t * (s * D.w)
        = D.w⁻¹ * (s⁻¹ * D.t * s) * D.w := by group
      _ = D.w⁻¹ * (D.u * D.t) * D.w := by rw [hsts]
      _ = D.t * D.u := by
          calc D.w⁻¹ * (D.u * D.t) * D.w
              = (D.w⁻¹ * D.u * D.w) * (D.w⁻¹ * D.t * D.w) := by group
            _ = D.u * D.t := by rw [hwu, hwt]
            _ = D.t * D.u := D.u_mul_t
  · calc (s * D.w)⁻¹ * (D.t * D.u) * (s * D.w)
        = D.w⁻¹ * (s⁻¹ * (D.t * D.u) * s) * D.w := by group
      _ = D.w⁻¹ * ((s⁻¹ * D.t * s) * (s⁻¹ * D.u * s)) * D.w := by group
      _ = D.w⁻¹ * ((D.u * D.t) * D.u) * D.w := by rw [hsts, hus]
      _ = D.w⁻¹ * D.t * D.w := by
          rw [show (D.u * D.t) * D.u = D.t by
            rw [mul_assoc, ← D.u_mul_t, ← mul_assoc, D.u_mul_u, one_mul]]
      _ = D.t := hwt

end CFSG.OddTranspositions.PartThree.Wong.SplitData
