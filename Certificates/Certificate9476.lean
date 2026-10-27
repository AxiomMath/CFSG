module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo1Inputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KMcertSound
import Certificates.Kernel.FusOps2.Facts

public section

open CertificateChecks.KernelAM CertificateChecks.KernelFusOps2

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9476 : fusCheck (ops2 24) NativeSporadic.Co1Seed1 NativeSporadic.Co1Seed2
    betaCo1P3N betaCo1P3Prog betaCo1P3 = true :=
  CFSG.KC.OpsF2K.fusCheck_of_K C1A.bind C1B.bind C1A.eq C1B.eq betaCo1P3_K

end Certificates
