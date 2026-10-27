module

public import Certificates.Data.Kernel.OpsW4N
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22W4Data
public import Certificates.Kernel.LocalComp.F3.Fi22

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.W4Fi22

open CFSG.KC.OpsW4N CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native

theorem fi22_K : w4L CFSG.KD.LC.F3.Fi22.lay CFSG.KD.LC.F3.Fi22.A CFSG.KD.LC.F3.Fi22.B fi22W4.base
    fi22W4.inv = true := by decide +kernel

def fi22Rep : Data := { fi22W4.base with outs := [299, 299, 753, 758] }

theorem fi22_neg : (!w4L CFSG.KD.LC.F3.Fi22.lay CFSG.KD.LC.F3.Fi22.A CFSG.KD.LC.F3.Fi22.B fi22Rep
    fi22W4.inv) = true := by decide +kernel

theorem fi22_neg_inv : (!w4L CFSG.KD.LC.F3.Fi22.lay CFSG.KD.LC.F3.Fi22.A CFSG.KD.LC.F3.Fi22.B
    fi22W4.base 299) = true := by decide +kernel

end CertificateChecks.KernelCensus.W4Fi22

end
