module

public import CFSG.RankThree.PartOne.CTP.FusionHeInputs
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.He

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate14956 : fusCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 heFusN
    heFusProg heFus = true :=
  CFSG.KC.OpsLayK.fusLP_sound He.lay_ok rfl rfl He.decA He.decB He.LA_eq He.LB_eq
    He.fus14956_K

end Certificates
