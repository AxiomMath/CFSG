module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusCo3Inputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KMcertSound
import Certificates.Kernel.FusOps2.Facts

public section

open CertificateChecks.KernelAM CertificateChecks.KernelFusOps2

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9473 : fusCheck (ops2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2
    betaCo3P3N betaCo3P3Prog betaCo3P3 = true :=
  CFSG.KC.OpsF2K.fusCheck_of_K C3A.bind C3B.bind C3A.eq C3B.eq betaCo3P3_K

end Certificates
