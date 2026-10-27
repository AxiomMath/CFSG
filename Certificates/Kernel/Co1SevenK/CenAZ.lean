module

public import Certificates.Kernel.Co1SevenK.CenData
public import Certificates.Data.Kernel.Co1Seven.Cen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KS.SporSch.M24

theorem kZA : centK CA.P CA.N (D.M Timmesfeld.Co1Seven.iT) = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
