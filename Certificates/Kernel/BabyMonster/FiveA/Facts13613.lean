module

public import CFSG.Certificates.Kernel.BabyMonster.FiveMFacts
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.All
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check5
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.FiveM.Basic
public import Certificates.Kernel.BabyMonster.FiveA.RankLin
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.RkA
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.RkAB
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.RkS

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM CFSG.KC.BM.FiveM

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "G1" => stripMat CFSG.KC.BM.Max15.g1
local notation "G2" => stripMat CFSG.KC.BM.Max15.g2

set_option maxRecDepth 100000

theorem pow_shift {M : Type*} [Monoid M] (a b : M) : ∀ n : ℕ, (a * b) ^ n * a = a * (b * a) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih : ∀ c : M, (a * b) ^ n * (a * c) = a * ((b * a) ^ n * c) := fun c => by
      rw [← mul_assoc, pow_shift a b n, mul_assoc]
    simp only [pow_succ, mul_assoc]
    exact ih (b * a)

theorem rank_conj {g c ci : MatB} (h : c * ci = 1) : (c * g * ci - 1).rank = (g - 1).rank := by
  have e : c * g * ci - 1 = c * (g - 1) * ci := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse h),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse h)]

theorem pow5 (a : MatB) : a * a * (a * a) * a = a ^ 5 := by
  simp only [pow_succ, pow_zero, one_mul]
  noncomm_ring

theorem fact13613 : Fact13613 G1 G2 := by
  have es : stripMat s = G2 ^ 14 := CertificateChecks.KernelBM.FiveM.s_eq
  have ey : stripMat y = G2 ^ 15 := CertificateChecks.KernelBM.FiveM.y_eq
  have es2 : stripMat s2 = stripMat s ^ 2 := by
    rw [← mul1 wf_s wf_s (by bm_strips4 CFSG.KC.BM.FiveM.cs2 69), sq]
  have es4 : stripMat s4 = stripMat s ^ 4 := by
    rw [← mul1 wf_s2 wf_s2 (by bm_strips4 CFSG.KC.BM.FiveM.cs4 69), es2, ← pow_add]
  have hs5 : (G2 ^ 14) ^ 5 = 1 := by
    rw [← es, ← one1 wf_s4 wf_s (by bm_strips4 CFSG.KC.BM.FiveM.sfive 69), es4, ← pow_succ]
  have ey1 : stripMat y1 = yOneW G1 G2 := CertificateChecks.KernelBM.FiveM.y1_eq
  have ew : stripMat w = yOneW G1 G2 * G2 ^ 15 := by
    rw [← mul1 wf_y1 wf_y (by bm_strips4 CFSG.KC.BM.FiveM.cw 69), ey1, ey]
  have ea : stripMat a = aW G1 G2 := by
    rw [← mul1 wf_w4 wf_w (by bm_strips4 CFSG.KC.BM.FiveM.ca 69),
      ← mul1 wf_w2 wf_w2 (by bm_strips4 CFSG.KC.BM.FiveM.cw4 69),
      ← mul1 wf_w wf_w (by bm_strips4 CFSG.KC.BM.FiveM.cw2 69), pow5, ew, aW]
  have ev : stripMat v = G2 ^ 15 * yOneW G1 G2 := by
    rw [← mul1 wf_y wf_y1 (by bm_strips4 CFSG.KC.BM.FiveM.cv 69), ey1, ey]
  have eb : stripMat b = bW G1 G2 := by
    rw [← mul1 wf_v4 wf_v (by bm_strips4 CFSG.KC.BM.FiveM.cb 69),
      ← mul1 wf_v2 wf_v2 (by bm_strips4 CFSG.KC.BM.FiveM.cv4 69),
      ← mul1 wf_v wf_v (by bm_strips4 CFSG.KC.BM.FiveM.cv2 69), pow5, ev, bW]
  have haa : aW G1 G2 * aW G1 G2 = 1 := by
    rw [← ea]
    exact one1 wf_a wf_a (by bm_strips4 CFSG.KC.BM.FiveM.asq 69)
  have hab : aW G1 G2 * bW G1 G2 = stripMat ab := by
    rw [← ea, ← eb]
    exact mul1 wf_a wf_b (by bm_strips4 CFSG.KC.BM.FiveM.cab 69)
  have hba : bW G1 G2 * aW G1 G2 = stripMat ab := by
    rw [← ea, ← eb]
    exact mul1 wf_b wf_a (by bm_strips4 CFSG.KC.BM.FiveM.ba 69)
  have has : aW G1 G2 * G2 ^ 14 = G2 ^ 14 * aW G1 G2 := by
    rw [← ea, ← es, mul1 (C := aS) wf_a wf_s (by bm_strips4 CFSG.KC.BM.FiveM.cas 69),
      mul1 (C := aS) wf_s wf_a (by bm_strips4 CFSG.KC.BM.FiveM.sa 69)]
  have hrs : (G2 ^ 14 - 1).rank = 3480 := by
    rw [← es]
    exact rank_sub_one_of_cert (by norm_num) wf_s wf_PrkS wf_RrkS
      (by bm_stripsx CFSG.KC.BM.FiveM.rkS_ 69) shape_rkS ech_rkS
  have hra : (aW G1 G2 - 1).rank = 2048 := by
    rw [← ea]
    exact rank_sub_one_of_cert (by norm_num) wf_a wf_PrkA wf_RrkA
      (by bm_stripsx CFSG.KC.BM.FiveM.rkA_ 69) shape_rkA ech_rkA
  have hrab : (aW G1 G2 * bW G1 G2 - 1).rank = 2048 := by
    rw [hab]
    exact rank_sub_one_of_cert (by norm_num) wf_ab wf_PrkAB wf_RrkAB
      (by bm_stripsx CFSG.KC.BM.FiveM.rkAB_ 69) shape_rkAB ech_rkAB
  have h70 : G2 ^ 70 = 1 := by rw [show 70 = 14 * 5 by norm_num, pow_mul, hs5]
  have hyy : G2 ^ 15 * G2 ^ 55 = 1 := by rw [← pow_add, h70]
  have hyy' : G2 ^ 55 * G2 ^ 15 = 1 := by rw [← pow_add, h70]
  have hby : bW G1 G2 * G2 ^ 15 = G2 ^ 15 * aW G1 G2 := by
    rw [bW, aW]
    exact pow_shift (G2 ^ 15) (yOneW G1 G2) 5
  have hb : bW G1 G2 = G2 ^ 15 * aW G1 G2 * G2 ^ 55 := by
    rw [← hby, mul_assoc, hyy, mul_one]
  have hbb : bW G1 G2 * bW G1 G2 = 1 := by
    rw [hb]
    calc G2 ^ 15 * aW G1 G2 * G2 ^ 55 * (G2 ^ 15 * aW G1 G2 * G2 ^ 55)
        = G2 ^ 15 * (aW G1 G2 * (G2 ^ 55 * G2 ^ 15) * aW G1 G2) * G2 ^ 55 := by
          simp only [mul_assoc]
      _ = 1 := by rw [hyy', mul_one, haa, mul_one, hyy]
  have hrb : (bW G1 G2 - 1).rank = 2048 := by rw [hb, rank_conj hyy, hra]
  have hcomm : ∀ k : ℕ, G2 ^ 14 * G2 ^ k = G2 ^ k * G2 ^ 14 := fun k => by
    rw [← pow_add, ← pow_add, add_comm]
  have hbs : bW G1 G2 * G2 ^ 14 = G2 ^ 14 * bW G1 G2 := by
    rw [hb]
    calc G2 ^ 15 * aW G1 G2 * G2 ^ 55 * G2 ^ 14 = G2 ^ 15 * (aW G1 G2 * G2 ^ 14) * G2 ^ 55 := by
          rw [mul_assoc, ← hcomm 55, ← mul_assoc, mul_assoc (G2 ^ 15)]
      _ = G2 ^ 14 * (G2 ^ 15 * aW G1 G2 * G2 ^ 55) := by
          rw [has, ← mul_assoc, ← hcomm 15]
          simp only [mul_assoc]
  exact ⟨hs5, ne_one_of_rank hrs (by norm_num), hrs, haa, ne_one_of_rank hra (by norm_num), hra,
    hbb, ne_one_of_rank hrb (by norm_num), hrb, by rw [hab, hba], hrab, has, hbs⟩

end CertificateChecks.KernelBM.FiveA

end
