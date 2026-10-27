
module

public import CFSG.Sporadic.Schreier.TitsStab
import Certificates.Kernel.LocalQT.Tits4139.Overgroups

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits in
theorem certificate4139 : ∀
    (M : Subgroup titsD),
    titsFlagStab ≤ M → M = titsFlagStab ∨ M = titsPointStab ∨ M = titsLineStab ∨ M = ⊤ :=
  fun M hM => KernelLocalQT.Tits4139.overgroups M hM

end Certificates
