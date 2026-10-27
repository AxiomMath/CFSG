module

public import Certificates.Kernel.Co1B.Dag24513
public import Certificates.Kernel.Co1B.Bfs24513
public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KS.SporSch.M24 CFSG.EvenSporadicStandard.TwoCo1.HypOne

@[expose] noncomputable def SM (l : Nat) : Nat := S2.M (sylIdxB.getD l 0)

theorem kQ : gtPinK SM 4 32769 ST.N ST.P ST.PAR ST.LAB ST.W ST.S = true := by quickRfl

end CertificateChecks.KernelCo1B.Syl2B

end
