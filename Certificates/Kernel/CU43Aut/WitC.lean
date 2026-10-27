module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.CU43Aut.SylData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

theorem kWC : bAnd(allN 191 (fun q => cK (WP q)), allN 3 (fun s => cK (SWP s))) = true := by
  quickRfl

end CertificateChecks.KernelCU43Aut

end
