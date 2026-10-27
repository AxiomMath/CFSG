module

public import Certificates.Kernel.Co1Five.Data
public import Certificates.Kernel.SporSch.Co1.Rows
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CertificateChecks.KernelCo1Five

open CFSG.KC.Enum CFSG.KS.Raw

theorem ch1023014bindA :
    bindListK 24 24 (TS 0) CertificateChecks.KernelSporSch.Co1Rows.RA.toList = true := by
  quickRfl

theorem ch1023014bindB :
    bindListK 24 24 (TS 1) CertificateChecks.KernelSporSch.Co1Rows.RB.toList = true := by
  quickRfl

end CertificateChecks.KernelCo1Five

end
