module

public import CFSG.Certificates.Kernel.BabyMonster.TcFive.All
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check0
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check1
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check10
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check11
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check12
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check13
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check14
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check15
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check16
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check17
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check18
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check19
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check2
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check20
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check21
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check22
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check23
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check24
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check25
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check26
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check3
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check4
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check5
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check6
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check7
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check8
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Check9
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.Wf

public section

namespace CertificateChecks.KernelBM.TcFive

open CFSG.KC.BM CFSG.KC.BM.TcFive CertificateChecks.KernelBM.FiveA

set_option maxRecDepth 100000

theorem e_q0 : stripMat E * stripMat Five.W_sq3 = stripMat Five.W_sq3 * stripMat E :=
  (mul1 (C := EQ) wf_E Five.wf_W_sq3 (by bm_strips4 CFSG.KC.BM.TcFive.c_EQ 69)).trans
    (mul1 Five.wf_W_sq3 wf_E (by bm_strips4 CFSG.KC.BM.TcFive.cm_eq0 69)).symm

theorem e_u : stripMat E * stripMat U = stripMat U * stripMat E :=
  (mul1 (C := EU) wf_E wf_U (by bm_strips4 CFSG.KC.BM.TcFive.c_EU 69)).trans
    (mul1 wf_U wf_E (by bm_strips4 CFSG.KC.BM.TcFive.cm_eu 69)).symm

theorem u_eq : stripMat U = stripMat Five.Q2 * stripMat Five.Q3_sq1 * stripMat Five.Q4 *
    stripMat Five.Zp4 := by
  rw [← mul1 wf_v121 Five.wf_Zp4 (by bm_strips4 CFSG.KC.BM.TcFive.c_U 69),
    ← mul1 wf_v120 Five.wf_Q4 (by bm_strips4 CFSG.KC.BM.TcFive.c_v121 69),
    ← mul1 Five.wf_Q2 Five.wf_Q3_sq1 (by bm_strips4 CFSG.KC.BM.TcFive.c_v120 69)]

theorem conj_a : stripMat Seeds.A1 * stripMat G = stripMat G * stripMat AP :=
  (mul1 (C := AG) Seeds.wf_A1 wf_G (by bm_strips4 CFSG.KC.BM.TcFive.c_AG 69)).trans
    (mul1 wf_G wf_AP (by bm_strips4 CFSG.KC.BM.TcFive.conjA 69)).symm

theorem conj_b : stripMat Seeds.A2 * stripMat G = stripMat G * stripMat BP :=
  (mul1 (C := BG) Seeds.wf_A2 wf_G (by bm_strips4 CFSG.KC.BM.TcFive.c_BG 69)).trans
    (mul1 wf_G wf_BP (by bm_strips4 CFSG.KC.BM.TcFive.conjB 69)).symm

theorem conj_i : stripMat G * stripMat Gi = 1 :=
  one1 wf_G wf_Gi (by bm_strips4 CFSG.KC.BM.TcFive.conjI 69)

end CertificateChecks.KernelBM.TcFive

end
