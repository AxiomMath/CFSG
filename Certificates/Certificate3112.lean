
module

public import Certificates.Certificate3112Base


public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

namespace CertificateChecks.Batch3112

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

end CertificateChecks.Batch3112

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Sp8 in
theorem certificate3112 : ∀ v : V8, qPoly v = 1 →
      (Finset.univ.filter fun w : V8 => qPoly (w + v) + 1 = 0).card = 136 :=
  fun v _ => CertificateChecks.Batch3112.card_zeros_one v

end Certificates
