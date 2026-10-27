module

public import Certificates.Kernel.Co1FiveL.TrData
public import Certificates.Data.Kernel.Co1Seven.Cen
public import Certificates.Data.Kernel.Co1ClosP
public import Certificates.Data.Kernel.SporSch.Co1Bfs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KS.SporSch.M24 CFSG.KC.Co1ClosP Timmesfeld.Co1Five

theorem kHG0 : bAnd(commGK (HG 0) 5 (HG 0 0), commGK (HG 0) 5 (HG 0 1)) = true := by quickRfl

theorem kHG1 : bAnd(commGK (HG 1) 6 (HG 1 0), commGK (HG 1) 6 (HG 1 1)) = true := by quickRfl

theorem kHG2 : bAnd(commGK (HG 2) 6 (HG 2 0), commGK (HG 2) 6 (HG 2 1)) = true := by quickRfl

theorem kHT0 : bAnd(Nat.beq HT0.N (nat_lit 125),
    gtPinK (HG 0) 5 100000 HT0.N HT0.P HT0.PAR HT0.LAB HT0.W HT0.S) = true := by quickRfl

theorem kHT2 : bAnd(Nat.beq HT2.N (nat_lit 250),
    gtPinK (HG 2) 6 100000 HT2.N HT2.P HT2.PAR HT2.LAB HT2.W HT2.S) = true := by quickRfl

theorem kCl2 : closPK HT2.P HT2.N [2] 5 0 F2.R F2.C F2.W = true := by quickRfl

end CertificateChecks.KernelCo1FiveL

end
