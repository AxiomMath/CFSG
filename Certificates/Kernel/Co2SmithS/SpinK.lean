module

public import Certificates.Data.Kernel.Co2SmithS.Spin

public section

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS

theorem spinK_ok : spinCheckK = true := by decide +kernel

end CertificateChecks.KernelCo2SmithS

end
