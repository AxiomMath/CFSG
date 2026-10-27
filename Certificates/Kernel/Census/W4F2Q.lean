module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.RankThree46F2.Co3
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1W4Data
public import Certificates.Kernel.AlphaMc.SeedsF2

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.W4F2

open CFSG.KC.OpsF2K CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native
  CertificateChecks.KernelAM

theorem co3_Q : w4Q 22 C3A.M C3B.M co3W3.base co3W3.inv = true := by decide +kernel

theorem co1_Q : w4Q 24 C1A.M C1B.M co1W4.base co1W4.inv = true := by decide +kernel

theorem co3_negQ :
    (!w4Q 22 C3A.M C3B.M { co3W3.base with outs := [43, 43, 49] } co3W3.inv) = true := by
  decide +kernel

theorem co3_neg_seedsQ : (!w4Q 22 C3B.M C3A.M co3W3.base co3W3.inv) = true := by decide +kernel

def co1RepQ : Data := { co1W4.base with outs := [627, 627, 748, 72] }

theorem co1_negQ : (!w4Q 24 C1A.M C1B.M co1RepQ co1W4.inv) = true := by decide +kernel

theorem co1_neg_invQ : (!w4Q 24 C1A.M C1B.M co1W4.base 1) = true := by decide +kernel

end CertificateChecks.KernelCensus.W4F2

end
