module

public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveAFacts
public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveA.All
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.FiveA.RankLin
public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveA.Check0
public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveA.Check1
public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveA.RkT
public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveA.RkY
public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveA.Wf

public section

namespace CertificateChecks.KernelBM.TwoDFiveA

open CFSG.KC.BM CFSG.KC.BM.TwoDFiveA CertificateChecks.KernelBM.FiveA

local notation "G" => stripMat CFSG.KC.BM.TwoDFiveA.g

set_option maxRecDepth 100000

theorem t_eq : stripMat t = G ^ 15 ∧ stripMat y = G ^ 6 := by
  have e2 : stripMat g2 = G ^ 2 := by
    rw [← mul1 wf_g wf_g (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_g2 69), sq]
  have e3 : stripMat g3 = G ^ 3 := by
    rw [← mul1 wf_g2 wf_g (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_g3 69), e2, ← pow_succ]
  have ey : stripMat y = G ^ 6 := by
    rw [← mul1 wf_g3 wf_g3 (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_y 69), e3, ← pow_add]
  have e12 : stripMat g12 = G ^ 12 := by
    rw [← mul1 wf_y wf_y (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_g12 69), ey, ← pow_add]
  refine ⟨?_, ey⟩
  rw [← mul1 wf_g12 wf_g3 (by bm_strips4 CFSG.KC.BM.TwoDFiveA.c_t 69), e12, e3, ← pow_add]

theorem fact101702 : Fact101702 (stripMat t) (stripMat y) := by
  obtain ⟨et, ey⟩ := t_eq
  have htt : stripMat t * stripMat t = 1 :=
    one1 wf_t wf_t (by bm_strips4 CFSG.KC.BM.TwoDFiveA.tsq 69)
  have h30 : G ^ 30 = 1 := by
    rw [← htt, et, ← pow_add]
  have hy5 : stripMat y ^ 5 = 1 := by
    rw [ey, ← pow_mul]
    exact h30
  have hty : stripMat t * stripMat y = stripMat y * stripMat t := by
    rw [et, ey, ← pow_add, ← pow_add, add_comm]
  have hrt : (stripMat t - 1).rank = 2168 :=
    rank_sub_one_of_cert (by norm_num) wf_t wf_PT wf_QT
      (by bm_stripsx CFSG.KC.BM.TwoDFiveA.rkT_ 69) shape_rkT ech_rkT
  have hry : (stripMat y - 1).rank = 3480 :=
    rank_sub_one_of_cert (by norm_num) wf_y wf_PY wf_QY
      (by bm_stripsx CFSG.KC.BM.TwoDFiveA.rkY_ 69) shape_rkY ech_rkY
  exact ⟨htt, ne_one_of_rank hrt (by norm_num), hy5, ne_one_of_rank hry (by norm_num), hty, hrt,
    hry⟩

end CertificateChecks.KernelBM.TwoDFiveA

end
