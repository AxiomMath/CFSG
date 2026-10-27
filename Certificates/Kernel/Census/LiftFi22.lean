module

public import Certificates.Data.Kernel.OpsV4
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22LiftData
public import Certificates.Kernel.LocalComp.F3.Fi22
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.LiftFi22

open CFSG.KC.OpsV4 CFSG.RankThree.PartTwo.Census

theorem fi22_K : liftL CFSG.KD.LC.F3.Fi22.lay CFSG.KD.LC.F3.Fi22.A CFSG.KD.LC.F3.Fi22.B fi22Lift =
    true := by quickRfl

end CertificateChecks.KernelCensus.LiftFi22

end
