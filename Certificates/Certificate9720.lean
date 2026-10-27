module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentSporHS5Inputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KFusQSound
import Certificates.Kernel.SectionRankHS.FactsQ

public section

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint
open CertificateChecks.KernelSRHS

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9720 : fusCheck (ops2 20) NativeSporadic.HSSeed1 NativeSporadic.HSSeed2
    fusHSFiveN fusHSFiveProg fusHSFive = true :=
  CFSG.KC.OpsF2K.fusCheck_of_Q SA.bind SB.bind SA.eq SB.eq fusFive_Q

end Certificates
