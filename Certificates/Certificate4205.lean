
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvWord
import Certificates.Kernel.J4Ov.G4205
public import Certificates.Kernel.J4Q.Mat

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Ov in
theorem certificate4205 : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ 4 →
    Hj ≤ Eg uJ 11 ⊔ (Eg uJ 11).map (MulAut.conj (uEl ℓ)).toMonoidHom ∧
      ∃ j < 11, uEl ℓ * uJ j * (uEl ℓ)⁻¹ ∉ Hj :=
  fun _ h1 h4 => KernelJ4Ov.genE4205 KernelJ4Q.matFacts h1 h4

end Certificates
