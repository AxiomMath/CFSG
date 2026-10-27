module

public import Certificates.Kernel.BabyMonster.RegMem
public import CFSG.Certificates.Kernel.BabyMonster.B11.All
public import CFSG.Certificates.Kernel.BabyMonster.Max15.All
public import CFSG.Certificates.Kernel.BabyMonster.Max15.CheckSq
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check5

public section

namespace CertificateChecks.KernelBM.B11Mem

open CFSG.KC.BM CFSG.KC.BM.Reg

theorem b11_mem : (∀ t ∈ [B11.y, B11.x0, B11.x1, B11.x2, B11.x3, B11.y2, B11.y4, B11.y8, B11.p01,
      B11.p12, B11.p23, B11.p02], wfMat t = true) ∧
    MemsOK [Seeds.A1, Seeds.A2] [B11.y, B11.x0, B11.x1, B11.x2, B11.x3, B11.y2, B11.y4, B11.y8,
      B11.p01, B11.p12, B11.p23, B11.p02] := by
  bm_mem_cert [CFSG.KC.BM.B11, CFSG.KC.BM.Max15, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.B11Mem

end
