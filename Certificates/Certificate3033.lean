
module

public import Certificates.Certificate3033Base


public section

open CFSG.Monster.B.Fischer

namespace CertificateChecks.Batch3033

open CFSG.Monster.B.Fischer

end CertificateChecks.Batch3033

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer in
theorem certificate3033 : ∀ i < 77, ∀ j < 77, hexCat (hCat i) = hexCat (hCat j) → i = j := CertificateChecks.Batch3033.hexCat_inj

end Certificates
