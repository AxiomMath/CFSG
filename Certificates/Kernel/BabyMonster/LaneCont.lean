module

public import Certificates.Kernel.BabyMonster.LaneBase
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Cont_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Cont_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Cont_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Cont_3

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Ln

set_option maxRecDepth 100000

theorem conts : ∀ i < 4370, contOK CFSG.KC.BM.Dyadic.Bs i = true :=
  contOK_of_lanes lnData (R := recOf CFSG.KC.BM.DyLane.CR.rows)
    (by forall_lt_consts CFSG.KC.BM.Dyadic.lnCont 274)

end CertificateChecks.KernelBM.Dy

end
