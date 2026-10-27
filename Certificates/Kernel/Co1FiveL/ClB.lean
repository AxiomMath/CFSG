module

public import Certificates.Kernel.Co1FiveL.TrData
public import Certificates.Data.Kernel.Co1ClosP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Co1ClosP

theorem kCl1 : closPK HT1.P HT1.N [3, 4] 5 1 F1.R F1.C F1.W = true := by quickRfl

end CertificateChecks.KernelCo1FiveL

end
