module

public import CFSG.RankThree.PartOne.CTP.FusionJ2Inputs
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.J2

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate14955 : fusCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2 j2FusN
    j2FusProg j2Fus = true :=
  CFSG.KC.OpsLayK.fusLP_sound J2.lay_ok rfl rfl J2.decA J2.decB J2.LA_eq J2.LB_eq
    J2.fus14955_K

end Certificates
