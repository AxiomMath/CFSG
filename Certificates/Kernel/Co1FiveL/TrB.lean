module

public import Certificates.Kernel.Co1FiveL.TrData
public import Certificates.Data.Kernel.SporSch.Co1Bfs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KS.SporSch.M24

theorem kHT1 : bAnd(Nat.beq HT1.N (nat_lit 1500),
    gtPinK (HG 1) 6 100000 HT1.N HT1.P HT1.PAR HT1.LAB HT1.W HT1.S) = true := by quickRfl

end CertificateChecks.KernelCo1FiveL

end
