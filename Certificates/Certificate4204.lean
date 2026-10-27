
module


public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvWord
import Certificates.Kernel.J4Ov.G4204
public import Certificates.Certificate3084

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.Quasithin.J4Ov in
theorem certificate4204 : (∀ ℓ < 7, ℓ ≠ 0 → ℓ ≠ 2 → uEl 2 ∈ Hj ⊔ Subgroup.zpowers (uEl ℓ)) ∧
    ∀ k < 7, k ≠ 0 → k ≠ 2 → uEl k ∈ Hj ⊔ Subgroup.zpowers (uEl 2) :=
  ⟨fun _ hℓ h0 h2 => KernelJ4Ov.maxTo4204 Certificates.certificate3084 hℓ h0 h2,
    fun _ hk h0 h2 => KernelJ4Ov.maxFrom4204 Certificates.certificate3084 hk h0 h2⟩

end Certificates
