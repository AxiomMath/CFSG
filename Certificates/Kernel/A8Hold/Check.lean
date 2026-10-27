module

public import Certificates.Data.Kernel.A8Hold

public section

namespace CertificateChecks.KernelA8Hold

open CFSG.KC.A8Hold

theorem a8Chk1_ok : a8Chk1 = true := by decide +kernel

theorem a8Chk2_ok : a8Chk2 = true := by decide +kernel

end CertificateChecks.KernelA8Hold
