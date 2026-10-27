module

public import Certificates.Data.Kernel.D4SylK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Syl

open CFSG.KC.D4SylK

theorem checkK : d4SylCheckK = true := by decide +kernel

end CertificateChecks.KernelD4Syl

end
