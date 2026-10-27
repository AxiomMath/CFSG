module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootBasic
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentFusion

public section

namespace CFSG.OddTranspositions.PartThree.Wong.RootData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] (D : RootData G)

private lemma hM_mul_thetaM_mul_inv (a : ZMod 5) :
    hM * thetaM a * hM⁻¹ = thetaM (-a) := by
  revert a
  decide

private lemma hM_mul_cM_mul_inv : hM * cM * hM⁻¹ = -cM := by decide

private lemma cM_mul_thetaM_one_cube : (cM * thetaM 1) ^ 3 = 1 := by decide

private lemma twist_apply (x : SL5) :
    D.twist x = D.c2⁻¹ * D.y⁻¹ * D.h2 * D.d x * D.h2⁻¹ * D.y * D.c2 := by
  change (MulAut.conj (D.h2⁻¹ * D.y * D.c2)⁻¹) (D.d x) =
    D.c2⁻¹ * D.y⁻¹ * D.h2 * D.d x * D.h2⁻¹ * D.y * D.c2
  rw [MulAut.conj_apply]
  simp only [mul_inv_rev, inv_inv]
  group

private lemma t_commute_c2 : Commute D.t D.c2 := D.t_commute_i2 cM

private lemma h2_mul_d_thetaM (a : ZMod 5) :
    D.h2 * D.d (thetaM a) * D.h2⁻¹ = D.q12 (.ofAdd a) := by
  calc
    D.h2 * D.d (thetaM a) * D.h2⁻¹
        = ((D.i2 hM * D.i1 (thetaM a)) * (D.i2 (thetaM a) * (D.i2 hM)⁻¹)) := by
          rw [show D.h2 = D.i2 hM from rfl, D.d_apply]
          group
    _ = ((D.i1 (thetaM a) * D.i2 hM) * (D.i2 (thetaM a) * (D.i2 hM)⁻¹)) := by
          rw [← (D.commute (thetaM a) hM).eq]
    _ = D.i1 (thetaM a) * (D.i2 hM * D.i2 (thetaM a) * (D.i2 hM)⁻¹) := by group
    _ = D.i1 (thetaM a) * D.i2 (hM * thetaM a * hM⁻¹) := by
          simp only [← map_mul, ← map_inv]
    _ = D.i1 (thetaM a) * D.i2 (thetaM (-a)) := by rw [hM_mul_thetaM_mul_inv]
    _ = D.q12 (.ofAdd a) := rfl

private lemma h2_mul_w_mul_h2_inv : D.h2 * D.w * D.h2⁻¹ = D.w * D.t := by
  calc
    D.h2 * D.w * D.h2⁻¹
        = ((D.i2 hM * D.i1 cM) * (D.i2 cM * (D.i2 hM)⁻¹)) := by
          rw [show D.h2 = D.i2 hM from rfl, show D.w = D.i1 cM * D.i2 cM from rfl]
          group
    _ = ((D.i1 cM * D.i2 hM) * (D.i2 cM * (D.i2 hM)⁻¹)) := by
          rw [← (D.commute cM hM).eq]
    _ = D.i1 cM * (D.i2 hM * D.i2 cM * (D.i2 hM)⁻¹) := by group
    _ = D.i1 cM * D.i2 (hM * cM * hM⁻¹) := by simp only [← map_mul, ← map_inv]
    _ = D.i1 cM * D.i2 (-cM) := by rw [hM_mul_cM_mul_inv]
    _ = D.i1 cM * (D.t * D.i2 cM) := by rw [D.i2_neg]
    _ = D.w * D.t := by
          rw [show D.w = D.i1 cM * D.i2 cM from rfl, (D.t_commute_i2 cM).eq]
          group

private lemma y_conj_wt :
    D.y⁻¹ * (D.w * D.t) * D.y = D.v * D.w * (D.t * D.u) := by
  have hw := D.outer.y_conj_w
  have ht := D.outer.y_conj_t
  rw [show D.y = D.s * D.w from rfl]
  calc
    (D.s * D.w)⁻¹ * (D.w * D.t) * (D.s * D.w)
        = ((D.s * D.w)⁻¹ * D.w * (D.s * D.w)) *
            ((D.s * D.w)⁻¹ * D.t * (D.s * D.w)) := by group
    _ = (D.v * D.w) * (D.t * D.u) := by rw [hw, ht]
    _ = D.v * D.w * (D.t * D.u) := rfl

private lemma c2_inv_mul_v_mul_c2 : D.c2⁻¹ * D.v * D.c2 = D.v * D.t := by
  calc
    D.c2⁻¹ * D.v * D.c2
        = ((D.i2 cM)⁻¹ * D.i1 hM) * (D.i2 hM * D.i2 cM) := by
          rw [show D.c2 = D.i2 cM from rfl, show D.v = D.i1 hM * D.i2 hM from rfl]
          group
    _ = (D.i1 hM * (D.i2 cM)⁻¹) * (D.i2 hM * D.i2 cM) := by
          rw [← ((D.commute hM cM).inv_right).eq]
    _ = D.i1 hM * ((D.i2 cM)⁻¹ * D.i2 hM * D.i2 cM) := by group
    _ = D.i1 hM * D.i2 (cM⁻¹ * hM * cM) := by simp only [← map_mul, ← map_inv]
    _ = D.i1 hM * D.i2 (-hM) := by rw [cM_inv_mul_hM_mul_cM, neg_hM]
    _ = D.i1 hM * (D.t * D.i2 hM) := by rw [D.i2_neg]
    _ = D.v * D.t := by
          rw [show D.v = D.i1 hM * D.i2 hM from rfl, (D.t_commute_i2 hM).eq]
          group

private lemma c2_inv_mul_w_mul_c2 : D.c2⁻¹ * D.w * D.c2 = D.w := by
  have h : Commute D.w D.c2 := (D.commute cM cM).mul_left (Commute.refl D.c2)
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

private lemma c2_inv_mul_t_mul_c2 : D.c2⁻¹ * D.t * D.c2 = D.t := by
  rw [mul_assoc, (t_commute_c2 D).eq, inv_mul_cancel_left]

private lemma c2_inv_mul_u_mul_c2 :
    D.c2⁻¹ * D.u * D.c2 = D.u * D.c1⁻¹ * D.c2 := by
  have h : D.c2 * D.u = D.u * D.c1 := (D.u_mul_i1 cM).symm
  have h' : D.c2⁻¹ * D.u = D.u * D.c1⁻¹ := by
    calc
      D.c2⁻¹ * D.u = D.c2⁻¹ * D.u * D.c1 * D.c1⁻¹ := by group
      _ = D.c2⁻¹ * (D.u * D.c1) * D.c1⁻¹ := by group
      _ = D.c2⁻¹ * (D.c2 * D.u) * D.c1⁻¹ := by rw [← h]
      _ = D.u * D.c1⁻¹ := by group
  rw [h']

private lemma c1_sq : D.c1 * D.c1 = D.t := by
  rw [show D.c1 = D.i1 cM from rfl, ← map_mul, ← pow_two, cM_sq, ← D.t_eq_i1]

private lemma c1_inv_mul_c2 : D.c1⁻¹ * D.c2 = D.t * D.w := by
  have hinv : D.c1⁻¹ = D.c1 * D.t := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_assoc, c1_sq D, D.t_mul_t]
  have htw : Commute D.t D.w := (D.t_commute_i1 cM).mul_right (D.t_commute_i2 cM)
  calc
    D.c1⁻¹ * D.c2 = (D.c1 * D.t) * D.c2 := by rw [hinv]
    _ = D.c1 * (D.t * D.c2) := by rw [mul_assoc]
    _ = D.c1 * (D.c2 * D.t) := by
          rw [show D.c2 = D.i2 cM from rfl, (D.t_commute_i2 cM).eq]
    _ = (D.c1 * D.c2) * D.t := by rw [← mul_assoc]
    _ = D.t * (D.c1 * D.c2) := htw.eq.symm

private lemma vtwutw_eq_tuv :
    (D.v * D.t) * D.w * D.t * (D.u * D.t * D.w) = D.t * D.u * D.v := by
  have htw : Commute D.t D.w := (D.d_commute_t cM).symm
  have huw : Commute D.u D.w := (D.d_commute_u cM).symm
  have huv : Commute D.u D.v := (D.d_commute_u hM).symm
  have htu : Commute D.t D.u := D.t_commute_u
  have htv : Commute D.t D.v := (D.d_commute_t hM).symm
  calc
    (D.v * D.t) * D.w * D.t * (D.u * D.t * D.w)
        = D.v * D.w * (D.u * D.t * D.w) := by
          rw [mul_assoc D.v D.t D.w, htw.eq, ← mul_assoc D.v D.w D.t,
            mul_assoc (D.v * D.w) D.t D.t, D.t_mul_t, mul_one]
    _ = D.v * (D.w * (D.u * (D.t * D.w))) := by group
    _ = D.v * (D.w * (D.u * (D.w * D.t))) := by rw [htw.eq]
    _ = D.v * ((D.w * D.u) * (D.w * D.t)) := by group
    _ = D.v * ((D.u * D.w) * (D.w * D.t)) := by rw [huw.eq.symm]
    _ = D.v * (D.u * (D.w * D.w) * D.t) := by group
    _ = D.v * (D.u * D.t) := by rw [D.w_mul_w, mul_one]
    _ = (D.v * D.u) * D.t := by group
    _ = (D.u * D.v) * D.t := by rw [huv.eq.symm]
    _ = D.u * (D.v * D.t) := by group
    _ = D.u * (D.t * D.v) := by rw [htv.eq.symm]
    _ = (D.u * D.t) * D.v := by group
    _ = (D.t * D.u) * D.v := by rw [htu.eq.symm]

private lemma c2_conj_vwtu :
    D.c2⁻¹ * (D.v * D.w * (D.t * D.u)) * D.c2 = D.t * D.u * D.v := by
  have huw : D.u * D.c1⁻¹ * D.c2 = D.u * D.t * D.w := by
    rw [mul_assoc D.u D.c1⁻¹ D.c2, c1_inv_mul_c2 D]
    group
  calc
    D.c2⁻¹ * (D.v * D.w * (D.t * D.u)) * D.c2
        = (D.c2⁻¹ * D.v * D.c2) * (D.c2⁻¹ * D.w * D.c2) *
            (D.c2⁻¹ * D.t * D.c2) * (D.c2⁻¹ * D.u * D.c2) := by group
    _ = (D.v * D.t) * D.w * D.t * (D.u * D.c1⁻¹ * D.c2) := by
          rw [c2_inv_mul_v_mul_c2 D, c2_inv_mul_w_mul_c2 D, c2_inv_mul_t_mul_c2 D,
            c2_inv_mul_u_mul_c2 D]
    _ = (D.v * D.t) * D.w * D.t * (D.u * D.t * D.w) := by rw [huw]
    _ = D.t * D.u * D.v := vtwutw_eq_tuv D

private lemma twist_thetaM (a : ZMod 5) : D.twist (thetaM a) = D.q4 (.ofAdd a) := by
  calc
    D.twist (thetaM a)
        = D.c2⁻¹ * (D.y⁻¹ * (D.h2 * D.d (thetaM a) * D.h2⁻¹) * D.y) * D.c2 := by
          rw [twist_apply D]
          group
    _ = D.c2⁻¹ * (D.y⁻¹ * D.q12 (.ofAdd a) * D.y) * D.c2 := by rw [h2_mul_d_thetaM D]
    _ = D.c2⁻¹ * D.q3 (.ofAdd a) * D.c2 := by rw [← D.q3_ofAdd]
    _ = D.q4 (.ofAdd a) := by rw [← D.q4_ofAdd]

private lemma twist_cM : D.twist cM = D.t * D.u * D.v := by
  calc
    D.twist cM
        = D.c2⁻¹ * (D.y⁻¹ * (D.h2 * D.d cM * D.h2⁻¹) * D.y) * D.c2 := by
          rw [twist_apply D]
          group
    _ = D.c2⁻¹ * (D.y⁻¹ * (D.w * D.t) * D.y) * D.c2 := by
          rw [show D.d cM = D.w from rfl, h2_mul_w_mul_h2_inv D]
    _ = D.c2⁻¹ * (D.v * D.w * (D.t * D.u)) * D.c2 := by rw [y_conj_wt D]
    _ = D.t * D.u * D.v := c2_conj_vwtu D

theorem twist_root_and_weyl_images :
    (∀ a : ZMod 5, D.twist (thetaM a) = D.q4 (.ofAdd a)) ∧ D.twist cM = D.t * D.u * D.v ∧
    (D.t * D.u * D.v * D.q4 (.ofAdd 1)) ^ 3 = 1 := by
  have htheta := twist_thetaM D
  have hc := twist_cM D
  refine ⟨htheta, hc, ?_⟩
  rw [← hc, ← htheta 1, ← map_mul, ← map_pow, cM_mul_thetaM_one_cube, map_one]

end CFSG.OddTranspositions.PartThree.Wong.RootData
