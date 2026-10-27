module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusHNInputs
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.HN

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9481 : fusCheck (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2
    betaHNP5N betaHNP5Prog betaHNP5 = true :=
  CFSG.KC.OpsLayK.fusLP_sound HN.lay_ok rfl rfl HN.decA HN.decB HN.LA_eq HN.LB_eq
    HN.fus9481_K

end Certificates
