module

public import Certificates.Kernel.Co2Smith.NJFixDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

theorem njFix_k0 : njFixK 0 256 = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
