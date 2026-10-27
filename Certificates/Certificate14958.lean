module

public import CFSG.RankThree.PartOne.CTP.FusionThInputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KFusQSound
import Certificates.Kernel.FusOps2.ThQ

public section

open CertificateChecks.KernelFusOps2

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate14958 : fusCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thFusN
    thFusProg thFus = true :=
  CFSG.KC.OpsF2K.fusCheck_of_Q TA.bind TB.bind TA.eq TB.eq thFus_Q

end Certificates
