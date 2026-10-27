module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusONInputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.ON

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9475 : fusCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    betaONP3N betaONP3Prog betaONP3 = true :=
  CFSG.KC.OpsLayK.fusL_sound ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq
    ON.fus9475_K

end Certificates
