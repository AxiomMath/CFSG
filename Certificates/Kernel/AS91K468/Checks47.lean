module

public import Certificates.Data.Kernel.AS91K468.K47
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K468

open Certificates.Kernel.AS91K468 Certificates.Kernel.HJ12K CFSG.KC.Mat12P

theorem ch89407_base : base47Q = true := by quickRfl

theorem ch89407_f : f47Q = true := by quickRfl

theorem ch89407_g : g47Q = true := by quickRfl

end CertificateChecks.KernelAS91K468
