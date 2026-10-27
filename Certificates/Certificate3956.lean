module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelK3MathieuData
import Certificates.Kernel.LocalComp.K3M22
import Certificates.Kernel.LocalComp.K3M23
import Certificates.Kernel.LocalComp.K3M24

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.Child3.SelK3 in
theorem certificate3956 : (CFSG.EvenSmallLie.Child3.SelK3.check m22K3 = true)
    ∧ (CFSG.EvenSmallLie.Child3.SelK3.check m23K3 = true)
    ∧ (CFSG.EvenSmallLie.Child3.SelK3.check m24K3 = true) :=
  ⟨KernelLC.K3.M22.check_m22, KernelLC.K3.M23.check_ok, KernelLC.K3.M24.check_ok⟩

end Certificates
