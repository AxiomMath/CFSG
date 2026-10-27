module

public import Certificates.Data.Kernel.AS91Split
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91Split

open Certificates.Kernel.AS91Split Certificates.Kernel.HJ12K CFSG.KC.Mat12P
  CFSG.Quasithin.H13.AS91.Two

theorem ch89409_s : sQ48 = true := by quickRfl

theorem ch89409_core : coreQ48 = true := by quickRfl

theorem ch89409_u : uQ48 = true := by quickRfl

theorem ch89409_cj : cjQ48 = true := by quickRfl

end CertificateChecks.KernelAS91Split
