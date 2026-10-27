module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2HSInputs
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsF2KFusQSound
import Certificates.Kernel.SectionRankHS.FactsQ

public section

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint
open CertificateChecks.KernelSRHS

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9583 : fusCheck (ops2 20) NativeSporadic.HSSeed1 NativeSporadic.HSSeed2
    fusD2HSN fusD2HSProg fusD2HS = true :=
  CFSG.KC.OpsF2K.fusCheck_of_Q SA.bind SB.bind SA.eq SB.eq fusD2_Q

end Certificates
