module

public import Certificates.Data.Kernel.A6OrdK
public import Certificates.Kernel.ONanA6.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelA6Ord

open CFSG.KC.Ord CFSG.KC.A6Ord

theorem ch26081 : chk26081 CFSG.KD.ONanA6.la = true := by quickRfl

end CertificateChecks.KernelA6Ord
