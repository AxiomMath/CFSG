module

public import CFSG.LargeExtraspecial.AS62C36RigidInputs
import Certificates.Kernel.AS62Rigid.Facts
import Certificates.Kernel.AS62Rigid.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.LargeExtraspecial in
theorem certificate19780 : (AS62.Rigid.rigidCheck () = true) ∧ (AS62.Rigid.bDistinct () = true) ∧
    (AS62.Rigid.p1Distinct () = true) ∧ (AS62.Rigid.p2Distinct () = true) :=
  ⟨KernelAS62.rigidCheck_true, KernelAS62.bDistinct_true, KernelAS62.p1Distinct_true,
    KernelAS62.p2Distinct_true⟩

end Certificates
