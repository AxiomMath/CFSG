module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.RankThree46F2.Th
public import Certificates.Kernel.EvenBN.Th8Bind

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.W4Th

open CFSG.KC.OpsF2K CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native CertificateChecks.Th8

theorem th_Q : w4Q 248 SA.M SB.M thW3.base thW3.inv = true := by decide +kernel

def thRepQ : Data := { thW3.base with outs := [66, 66, 77] }

theorem th_negQ : (!w4Q 248 SA.M SB.M thRepQ thW3.inv) = true := by decide +kernel

theorem th_neg_invQ : (!w4Q 248 SA.M SB.M thW3.base 1) = true := by decide +kernel

end CertificateChecks.KernelCensus.W4Th

end
