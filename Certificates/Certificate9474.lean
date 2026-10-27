module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo2Inputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KMcertSound
import Certificates.Kernel.FusOps2.Facts

public section

open CertificateChecks.KernelAM CertificateChecks.KernelFusOps2

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9474 : fusCheck (ops2 22) NativeSporadic.Co2Seed1 NativeSporadic.Co2Seed2
    betaCo2P3N betaCo2P3Prog betaCo2P3 = true :=
  CFSG.KC.OpsF2K.fusCheck_of_K C2A.bind C2B.bind C2A.eq C2B.eq betaCo2P3_K

end Certificates
