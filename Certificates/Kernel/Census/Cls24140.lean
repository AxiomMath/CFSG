module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus.Cls24140

open CFSG.EvenSporadicStandard.Wong77.Cls

theorem cyc : checkCyc = true := by quickRfl

theorem one0 : checkOne 0 = true := by quickRfl

theorem one1 : checkOne 1 = true := by quickRfl

theorem cls : clsCheck = true := by
  unfold clsCheck
  rw [cyc, one0, one1]
  rfl

end CertificateChecks.KernelCensus.Cls24140
