
module

public import Certificates.Certificate3061Base

public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import Certificates.Kernel.MonsterB.Co2Mem
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3061

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CertificateChecks.KernelMonB

end CertificateChecks.Batch3061

namespace Certificates

open CertificateChecks.Batch3061 in
open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary in
theorem certificate3061 : (Native.vectors[0]! = 6144)
    ∧ (∀ i < 21, spanIdxN.getD i 0 < 891 ∧
       n6VecArr[spanIdxN.getD i 0]! = n6SpanArr[i]!) :=
  ⟨shortVec_zero, spanIdxN_ok⟩

end Certificates
