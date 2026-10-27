module

public import Certificates.Kernel.BabyMonster.RegTabMat
public import CFSG.Certificates.Kernel.BabyMonster.B31.All
public import CFSG.Certificates.Kernel.BabyMonster.Max5.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import Certificates.Data.BThirtyOne
public import CFSG.Certificates.Kernel.BabyMonster.B31.Check0
public import CFSG.Certificates.Kernel.BabyMonster.B31.Check1
public import CFSG.Certificates.Kernel.BabyMonster.B31.Check2
public import CFSG.Certificates.Kernel.BabyMonster.B31.Check3
public import CFSG.Certificates.Kernel.BabyMonster.B31.Check4
public import CFSG.Certificates.Kernel.BabyMonster.B31.Check5
public import CFSG.Certificates.Kernel.BabyMonster.B31.Rel
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check7

public section

namespace CertificateChecks.KernelBM.B31

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.LocalAnalysis.AGL81I.Section3.SporBig.BThirtyOneNative

theorem bThirtyOne_regs : RegsOK (bThirtyOneProg ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true
    [3, 2] [B31.a, B31.f3] := by
  bm_reg_cert_mat [CFSG.KC.BM.B31, CFSG.KC.BM.Max5, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.B31

end
