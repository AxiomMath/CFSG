module

public import Certificates.Data.Kernel.OpsW4N
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Data.RankThree46Odd.Ly
public import Certificates.Kernel.SporSch.Ly.BSData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.W4Ly

open CFSG.KC.OpsW4N CFSG.KC.OpsK CFSG.KC.Ord CFSG.KD.OrdLy CFSG.RankThree.PartTwo.Census
  CFSG.SectionRank.Native CertificateChecks.KernelSporSch

theorem ly_K : w4N (opsFpK 5 12 1332 111 8 L H CM RM ONE) LyBS.A LyBS.B lyW3.base lyW3.inv =
    true := by quickRfl

def lyRep : Data := { lyW3.base with outs := [247, 247, 496] }

theorem ly_neg : (!w4N (opsFpK 5 12 1332 111 8 L H CM RM ONE) LyBS.A LyBS.B lyRep lyW3.inv) =
    true := by quickRfl

theorem ly_neg_inv : (!w4N (opsFpK 5 12 1332 111 8 L H CM RM ONE) LyBS.A LyBS.B lyW3.base 247) =
    true := by quickRfl

end CertificateChecks.KernelCensus.W4Ly

end
