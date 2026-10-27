
module

public import Certificates.Certificate17030Base
import all Certificates.Certificate17030Base

public import Certificates.Certificate3120

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3Cover CFSG.Open CFSG.QuasithinUnique.A5.Delta5

namespace CertificateChecks.Batch17030

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3Cover CFSG.Open CFSG.QuasithinUnique.A5.Delta5

end CertificateChecks.Batch17030

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3Cover CFSG.Open CFSG.QuasithinUnique.A5.Delta5 in
theorem certificate17030 : ∀ v : Fin 5 → ZMod 2, isEven v →
    (∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → pact σ v = v) → v = 0 := by
  exact @CertificateChecks.Batch17030.fixed_alt_zero'_0

end Certificates
