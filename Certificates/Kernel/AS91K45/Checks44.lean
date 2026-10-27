module

public import Certificates.Data.Kernel.AS91K45.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K45

open Certificates.Kernel.AS91K45 Certificates.Kernel.HJ12K CFSG.KC.Mat12P CFSG.KC.Mat8P

theorem ch89405_stab1 : stab1OK = true := by quickRfl

theorem ch89405_stab : ok44Stab = true := by quickRfl

theorem ch89405_grp : ok44Grp = true := by quickRfl

theorem ch89405_w5 : ok44W5 = true := by quickRfl

theorem ch89405_perp : ok44Perp = true := by quickRfl

end CertificateChecks.KernelAS91K45
