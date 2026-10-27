module

public import Certificates.Kernel.BabyMonster.ProgTab
public import CFSG.Certificates.Kernel.BabyMonster.BProg.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check0
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check1
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check10
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check11
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check12
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check13
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check14
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check15
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check16
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check17
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check18
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check19
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check2
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check20
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check3
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check4
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check5
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check6
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check7
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check8
public import CFSG.Certificates.Kernel.BabyMonster.BProg.Check9

public section

namespace CertificateChecks.KernelBM.Run9201

open CFSG.KC.BM CFSG.KC.BM.B9201

@[expose] noncomputable def tL : List (List ℕ) :=
  [BProg.t1, BProg.t2, BProg.t3, BProg.t4, BProg.t5, BProg.t6, BProg.t7, BProg.t8, BProg.t9,
    BProg.t10, BProg.t11]

theorem bProg_strip : ∀ k < tL.length,
    runM CFSG.Sporadic.Bridge.B.bProg (stripMat Seeds.A1) (stripMat Seeds.A2)
      (CFSG.Sporadic.Bridge.B.bTreg k) = stripMat (tL.getD k []) ∧ wfMat (tL.getD k []) = true := by
  bm_prog_cert CFSG.KC.BM.BProg CFSG.KC.BM.Seeds.wf_A1 CFSG.KC.BM.Seeds.wf_A2

theorem tM_strip (k : ℕ) (hk : k < 11) :
    tM (stripMat Seeds.A1) (stripMat Seeds.A2) k = stripMat (tL.getD k []) ∧
      wfMat (tL.getD k []) = true :=
  bProg_strip k hk

end CertificateChecks.KernelBM.Run9201

end
