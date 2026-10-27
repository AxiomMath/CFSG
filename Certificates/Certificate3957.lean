module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporData
import Certificates.Kernel.LocalComp.K3J2
import Certificates.Kernel.LocalComp.K3HS
import Certificates.Kernel.LocalComp.K3McL
import Certificates.Kernel.LocalComp.K3He

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Child3.SelK3 in
theorem certificate3957 : (check j2K3 = true)
    ∧ (check hsK3 = true)
    ∧ (check mclK3 = true)
    ∧ (check heK3 = true) :=
  ⟨KernelLC.K3.J2.check_ok, KernelLC.K3.HS.check_ok, KernelLC.K3.McL.check_ok,
    KernelLC.K3.He.check_ok⟩

end Certificates
