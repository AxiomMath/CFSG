module

public import Certificates.Data.Kernel.ASVolI.K43K

public section

namespace CertificateChecks.KernelASVolI

open CFSG.KS.ASVolI

theorem k43_octOKK : octOKK = true := by
  decide +kernel

theorem k43_ptChainK : ptChainK = true := by
  decide +kernel

theorem k43_vecChainK : vecChainK = true := by
  decide +kernel

end CertificateChecks.KernelASVolI

end
