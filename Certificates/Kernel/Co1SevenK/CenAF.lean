module

public import Certificates.Kernel.Co1SevenK.CenData
public import Certificates.Data.Kernel.Co1Seven.Cen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KS.SporSch.M24

theorem kFA : closK CA.P CA.N FA.R FA.C FA.W = true := by quickRfl

end CertificateChecks.KernelCo1SevenK

end
