module

public import Certificates.Kernel.AE6F.Checks
public import Certificates.Data.Kernel.A6h2SwapK

public section

namespace CertificateChecks.KernelA6h2

open CertificateChecks.KernelAE6F CFSG.KC.A6h2Swap

theorem swapK_ok : swapKN RG = true := by decide +kernel

end CertificateChecks.KernelA6h2
