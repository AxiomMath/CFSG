
module

public import Certificates.Certificate3077Base

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase

public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

namespace CertificateChecks.Batch3077

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

end CertificateChecks.Batch3077

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Sp8 in
theorem certificate3077 : ∀ v : V8, ∑ i, ∑ j, v i * gram0 i j * v j = 0 :=
  CertificateChecks.Batch3077.sum_alt gram0 CertificateChecks.Batch3077.gram0_symm CertificateChecks.Batch3077.gram0_diag

end Certificates
