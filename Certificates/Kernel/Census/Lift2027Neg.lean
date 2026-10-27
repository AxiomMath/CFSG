module

public import Certificates.Kernel.SporSch.Ly.BSData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus.Lift2027

open CertificateChecks.KernelSporSch.LyBS

theorem neg87 : (!Nat.beq (mul (CF 8) (CF 7)) A) = true := by quickRfl

theorem neg77 : (!Nat.beq (mul (CF 7) (CF 7)) A) = true := by quickRfl

end CertificateChecks.KernelCensus.Lift2027
