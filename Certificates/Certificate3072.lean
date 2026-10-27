
module

public import Certificates.Certificate3072Base


public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B

namespace CertificateChecks.Batch3072

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B

end CertificateChecks.Batch3072

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Sp8 in
theorem certificate3072 : ∀ k < 44, h1ConjN k (false, 0, 191) = (false, 0, 191) := by
  exact CertificateChecks.Batch3072.h1Conj_fix_0

end Certificates
