module

public import CFSG.RankThree.PartOne.CTP.FusionSuzInputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.Suz

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate14957 : fusCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 suzFusN
    suzFusProg suzFus = true :=
  CFSG.KC.OpsLayK.fusL_sound Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq
    Suz.fus14957_K

end Certificates
