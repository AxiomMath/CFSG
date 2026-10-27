module

public import Certificates.Data.Kernel.AS91S42
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91S42

open Certificates.Kernel.AS91S42

theorem ch89402_s1 : stabQ 3 g1Q p1Q w1Q 3840 32 = true := by quickRfl

theorem ch89402_s2 : stabQ 5 g2Q p2Q w2Q 1920 16 = true := by quickRfl

end CertificateChecks.KernelAS91S42
