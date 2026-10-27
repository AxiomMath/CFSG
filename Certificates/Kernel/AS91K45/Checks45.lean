module

public import Certificates.Data.Kernel.AS91K45.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K45

open Certificates.Kernel.AS91K45 Certificates.Kernel.HJ12K CFSG.KC.Mat12P CFSG.KC.Mat8P

theorem ch89404_stab1 : stab1OK = true := by quickRfl

theorem ch89404_orb : ok45Orb = true := by quickRfl

theorem ch89404_stab : ok45Stab = true := by quickRfl

theorem ch89404_p : ok45P = true := by quickRfl

end CertificateChecks.KernelAS91K45
