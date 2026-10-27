module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusJ3Inputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KMcertSound
import Certificates.Kernel.FusOps2.Facts

public section

open CertificateChecks.KernelJ3L CertificateChecks.KernelFusOps2

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9470 : fusCheck (ops2 80) NativeSporadic.J3Seed1 NativeSporadic.J3Seed2
    betaJ3P3N betaJ3P3Prog betaJ3P3 = true :=
  CFSG.KC.OpsF2K.fusCheck_of_K JA.bind JB.bind JA.eq JB.eq betaJ3P3_K

end Certificates
