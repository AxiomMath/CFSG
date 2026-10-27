module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3SporDataB
import Certificates.Kernel.LocalComp.K3Suz
import Certificates.Kernel.LocalComp.K3Co3
import Certificates.Kernel.LocalComp.K3Co2

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Child3.SelK3 in
theorem certificate3958 : (check suzK3 = true)
    ∧ (check co3K3 = true)
    ∧ (check co2K3 = true) :=
  ⟨KernelLC.K3.Suz.check_ok, KernelLC.K3.Co3.check_ok, KernelLC.K3.Co2.check_ok⟩

end Certificates
