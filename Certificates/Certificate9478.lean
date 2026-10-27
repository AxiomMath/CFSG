module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusFi22Inputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.Fi22

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9478 : fusCheck (ops3 77) NativeSporadic.Fi22Seed1 NativeSporadic.Fi22Seed2
    betaFi22P3N betaFi22P3Prog betaFi22P3 = true :=
  CFSG.KC.OpsLayK.fusL_sound Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB Fi22.LA_eq Fi22.LB_eq
    Fi22.fus9478_K

end Certificates
