module

public import Certificates.Data.E4QuatSp6Check
import CFSG.Certificates.Kernel.PermCent.Sp6E4QuatSound
import Certificates.Kernel.PermCent.K124A
import Certificates.Kernel.PermCent.K124T
import Certificates.Kernel.PermCent.K124I
import Certificates.Kernel.PermCent.K124J

public section

open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.Certificates.Kernel.PkCV
  CFSG.Certificates.Kernel.PkCV.Sp6E

namespace Certificates

open CertificateChecks

theorem certificate124 : CFSG.ClassicalInvolution.Q3.TL4.E4Sp6.check () = true := by
  have ha := KernelPermCent.k124a
  rw [p124a.eq_1, Bool.and_eq_true, Bool.and_eq_true] at ha
  rw [check_eq124, ha.1.1, ha.1.2, ha.2, KernelPermCent.k124i1, KernelPermCent.k124i2,
    KernelPermCent.k124i3, KernelPermCent.k124i4, KernelPermCent.k124m, KernelPermCent.k124t,
    KernelPermCent.k124n]
  rfl

end Certificates
