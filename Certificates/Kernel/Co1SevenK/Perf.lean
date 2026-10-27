module

public import Certificates.Kernel.Co1SevenK.Dag
public import Certificates.Data.Kernel.Co1Seven.Perf
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open Timmesfeld.Co1Seven Timmesfeld.Co1SevenPerfect

theorem kPerf : perfK D.M D.MI D.N (D.M iT) = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
