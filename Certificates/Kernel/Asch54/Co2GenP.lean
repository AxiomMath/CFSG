module

public import Certificates.Kernel.Asch54.Co2Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAsch54.Co2

open CFSG.KC.Enum CFSG.KS

theorem genPA : allN 6 (fun j => inPK (ch75342a.S j)) = true := by
  quickRfl

theorem genPB : allN 5 (fun j => inPK (ch75342b.S j)) = true := by
  quickRfl

end CertificateChecks.KernelAsch54.Co2

end
