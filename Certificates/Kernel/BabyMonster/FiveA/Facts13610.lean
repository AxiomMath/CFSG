module

public import CFSG.Certificates.Kernel.BabyMonster.FiveAFacts
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check0
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check14
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkT
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkU
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkYA
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkZ
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Wf
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.FiveA.RankLin

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM CFSG.KC.BM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "MX" => stripMat CFSG.KC.BM.Five.f85
local notation "MH" => stripMat CFSG.KC.BM.Five.f86

set_option maxRecDepth 100000

theorem a1_eq : stripMat a1 = MX * MH ^ 4 * MX ^ 4 := by
  rw [← mul2 Five.wf_f85 Five.wf_f86_sq2 Five.wf_f85_sq2
    (by bm_strips4 CFSG.KC.BM.FiveA.ca1 69), h_sq2, x_sq2]

theorem p2_eq : stripMat p2 = MH ^ 2 * MH ^ 4 := by
  rw [← mul1 Five.wf_f86_sq1 Five.wf_f86_sq2 (by bm_strips4 CFSG.KC.BM.FiveA.cp2 69), h_sq1,
    h_sq2]

theorem a3_eq : stripMat a3 = MH ^ 7 * stripMat a1 * stripMat p2 * stripMat a1 * MH ^ 3 *
    stripMat a1 * MH ^ 4 := by
  have e := stripMat_mul_of_allStrips (Ws := [a1, p2, a1, Five.H3, a1, Five.f86_sq2]) (C := a3)
    (by simp [wf_a1, wf_p2, Five.wf_H3, Five.wf_f86_sq2]) Five.wf_oh_p
    (by bm_strips4 CFSG.KC.BM.FiveA.ca3 69)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [← e, h_p, h_three, h_sq2]

theorem uWord_eq : uWord MX MH = stripMat a3 := by
  have e5 : MH ^ 5 = ((hU⁻¹ ^ 3 : MatBˣ) : MatB) := by
    rw [Units.val_pow_eq_pow_val]
    change MH ^ 5 = (MH ^ 7) ^ 3
    rw [← pow_mul, show 7 * 3 = 5 + 8 + 8 by norm_num, h_pow_mod, h_pow_mod]
  have e6 : MH ^ 2 * MH ^ 4 = ((hU⁻¹ ^ 2 : MatBˣ) : MatB) := by
    rw [Units.val_pow_eq_pow_val]
    change MH ^ 2 * MH ^ 4 = (MH ^ 7) ^ 2
    rw [← pow_add, ← pow_mul, show 7 * 2 = 2 + 4 + 8 by norm_num, h_pow_mod]
  have e7 : MH ^ 7 = ((hU⁻¹ : MatBˣ) : MatB) := rfl
  have e3 : MH ^ 3 = ((hU ^ 3 : MatBˣ) : MatB) := (Units.val_pow_eq_pow_val hU 3).symm
  have e4 : MH ^ 4 = ((hU ^ 4 : MatBˣ) : MatB) := (Units.val_pow_eq_pow_val hU 4).symm
  have ex4 : MX ^ 4 = ((xU⁻¹ : MatBˣ) : MatB) := rfl
  have eh : MH = ((hU : MatBˣ) : MatB) := rfl
  have ex : MX = ((xU : MatBˣ) : MatB) := rfl
  rw [a3_eq, a1_eq, p2_eq, uWord, e6, e7, e5, e3, e4, ex4, eh, ex]
  simp only [← Units.val_mul]
  refine congrArg Units.val ?_
  group

theorem fact13610 : Fact13610 MX MH := by
  have huu : stripMat a3 * stripMat a3 = 1 :=
    one1 wf_a3 wf_a3 (by bm_strips4 CFSG.KC.BM.FiveA.uu 69)
  have hrT : (MH ^ 4 - 1).rank = 2048 := by
    rw [← h_sq2]
    exact rank_sub_one_of_cert (by norm_num) Five.wf_f86_sq2 wf_PrkT wf_RrkT
      (by bm_stripsx CFSG.KC.BM.FiveA.rkT_ 69) shape_rkT ech_rkT
  have hrU : (stripMat a3 - 1).rank = 2048 :=
    rank_sub_one_of_cert (by norm_num) wf_a3 wf_PrkU wf_RrkU
      (by bm_stripsx CFSG.KC.BM.FiveA.rkU_ 69) shape_rkU ech_rkU
  refine ⟨hrT, ?_, ?_, ?_⟩
  · rw [uWord_eq]
    exact huu
  · rw [uWord_eq]
    exact ne_one_of_rank hrU (by norm_num)
  · rw [uWord_eq]
    exact hrU

theorem fact13612 : Fact13612 MX MH := by
  have hq1 : qOneW MX MH = stripMat Five.W_sq3 := q_one.symm
  have hq2 : qTwoW MX MH = stripMat Five.Q2 := by rw [qTwoW, hq1, q_two]
  have hq3 : qThreeW MX MH = stripMat Five.Q3 := by rw [qThreeW, hq1, q_three]
  have hb4 : stripMat Five.Q2 * stripMat Five.Q3 = stripMat b4 :=
    mul1 Five.wf_Q2 Five.wf_Q3 (by bm_strips4 CFSG.KC.BM.FiveA.cb4 69)
  have hb5 : stripMat Five.f86_sq2 * stripMat b4 = stripMat b5 :=
    mul1 Five.wf_f86_sq2 wf_b4 (by bm_strips4 CFSG.KC.BM.FiveA.cb5 69)
  have hty : stripMat b4 * stripMat Five.f86_sq2 = stripMat b5 :=
    mul1 wf_b4 Five.wf_f86_sq2 (by bm_strips4 CFSG.KC.BM.FiveA.tya 69)
  have hz : qOneW MX MH ^ 4 * qTwoW MX MH ^ 4 * qOneW MX MH * qTwoW MX MH =
      stripMat Five.Z := by
    have e := stripMat_mul_eq_of_allStrips2 (Ws := [Five.W_sq3, Five.Z]) (Ds := [Five.Q2])
      (by simp [Five.wf_W_sq3, Five.wf_Z]) (by simp [Five.wf_Q2]) Five.wf_Q2 Five.wf_W_sq3
      (by bm_strips2 CFSG.KC.BM.Five.cZ 69)
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
    have q5 := q_five
    let q1U : MatBˣ := ⟨stripMat Five.W_sq3, stripMat Five.W_sq3 ^ 4,
      by rw [← pow_succ', q5], by rw [← pow_succ, q5]⟩
    let q2U : MatBˣ := hU⁻¹ * q1U * hU
    have hq2U : (q2U : MatB) = stripMat Five.Q2 := by
      rw [q_two]
      rfl
    have h1p : q1U ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact q5)
    have h2p : q2U ^ 5 = 1 := by
      change (hU⁻¹ * q1U * hU) ^ 5 = 1
      rw [conj_pow', h1p]
      group
    have i1 : q1U ^ 4 = q1U⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h1p])
    have i2 : q2U ^ 4 = q2U⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h2p])
    rw [← hq2U] at e
    have hZu : stripMat Five.Z = (((q2U * q1U)⁻¹ * q1U * q2U : MatBˣ) : MatB) := by
      calc stripMat Five.Z
          = (((q2U * q1U)⁻¹ : MatBˣ) : MatB) * (((q2U * q1U : MatBˣ) : MatB) * stripMat Five.Z) := by
            rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        _ = (((q2U * q1U)⁻¹ : MatBˣ) : MatB) * ((q1U : MatB) * (q2U : MatB)) := by
            rw [Units.val_mul, e]
        _ = (((q2U * q1U)⁻¹ * q1U * q2U : MatBˣ) : MatB) := by
            simp only [Units.val_mul, mul_assoc]
    rw [hq1, hq2, ← hq2U, hZu]
    change ((q1U : MatB)) ^ 4 * (q2U : MatB) ^ 4 * (q1U : MatB) * (q2U : MatB) = _
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, i1, i2]
    simp only [← Units.val_mul]
    refine congrArg Units.val ?_
    group
  refine ⟨?_, ?_, ?_⟩
  · rw [hq2, hq3, hb4, ← h_sq2, hb5, hty]
  · rw [hq2, hq3, hb4]
    exact rank_sub_one_of_cert (by norm_num) wf_b4 wf_PrkYA wf_RrkYA
      (by bm_stripsx CFSG.KC.BM.FiveA.rkYA_ 69) shape_rkYA ech_rkYA
  · rw [hz]
    exact rank_sub_one_of_cert (by norm_num) Five.wf_Z wf_PrkZ wf_RrkZ
      (by bm_stripsx CFSG.KC.BM.FiveA.rkZ_ 69) shape_rkZ ech_rkZ

end CertificateChecks.KernelBM.FiveA

end
