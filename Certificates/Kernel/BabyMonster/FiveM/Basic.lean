module

public import CFSG.Certificates.Kernel.BabyMonster.FiveMFacts
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.Check0
public import CFSG.Certificates.Kernel.BabyMonster.FiveM.Wf
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check0
public import Certificates.Kernel.BabyMonster.FiveA.Basic

public section

namespace CertificateChecks.KernelBM.FiveM

open CFSG.KC.BM CFSG.KC.BM.FiveM CertificateChecks.KernelBM.FiveA

local notation "G1" => stripMat CFSG.KC.BM.Max15.g1
local notation "G2" => stripMat CFSG.KC.BM.Max15.g2

set_option maxRecDepth 100000

theorem s_eq : stripMat s = G2 ^ 14 := by
  have e16 : stripMat Max15.r16 = G2 ^ 2 := by
    rw [← mul1 wf_g2 wf_g2 (by bm_strips4 CFSG.KC.BM.Max15.c_r16 69), sq]
  have e4 : stripMat q4 = G2 ^ 4 := by
    rw [← mul1 wf_r16 wf_r16 (by bm_strips4 CFSG.KC.BM.FiveM.cq4 69), e16, ← pow_add]
  have e8 : stripMat q8 = G2 ^ 8 := by
    rw [← mul1 wf_q4 wf_q4 (by bm_strips4 CFSG.KC.BM.FiveM.cq8 69), e4, ← pow_add]
  have e12 : stripMat q12 = G2 ^ 12 := by
    rw [← mul1 wf_q8 wf_q4 (by bm_strips4 CFSG.KC.BM.FiveM.cq12 69), e8, e4, ← pow_add]
  rw [← mul1 wf_q12 wf_r16 (by bm_strips4 CFSG.KC.BM.FiveM.cs 69), e12, e16, ← pow_add]

theorem y_eq : stripMat y = G2 ^ 15 := by
  rw [← mul1 wf_s wf_g2 (by bm_strips4 CFSG.KC.BM.FiveM.cy 69), s_eq, ← pow_succ]

theorem g1c_eq : stripMat g1c = G1 ^ 3 := by
  rw [← mul2 wf_g1 wf_g1 wf_g1 (by bm_strips4 CFSG.KC.BM.FiveM.cg1c 69), pow_three']

theorem y1_eq : stripMat y1 = yOneW G1 G2 := by
  rw [← mul2 wf_g1 wf_y wf_g1c (by bm_strips4 CFSG.KC.BM.FiveM.cy1 69), y_eq, g1c_eq, yOneW]

end CertificateChecks.KernelBM.FiveM

end
