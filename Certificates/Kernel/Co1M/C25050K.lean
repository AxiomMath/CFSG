module

public import Certificates.Kernel.Co1M.Regs10072
public import Certificates.Data.Kernel.Co1M.MW3K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.EvenSporadicStandard.TwoB.MW3 CFSG.KC.Co1F2 CFSG.Sporadic.Co1.OddNative

theorem c25050_chk :
    commOKOn (runRows (cmRP3.map (unpackRK 24)).toArray extraLines)
      (unpackRK 24 (getL 0 cmRP71 27)) = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end
