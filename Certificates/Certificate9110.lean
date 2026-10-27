module

public import CFSG.Sporadic.Presentation.Fi22ExactWalksInputs
import Certificates.Kernel.Fi22F.Agree

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.Fi22Exact in
open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration in
theorem certificate9110 : ∀ pp ∈ allPairs,
    (evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk})
        (gW pp.1.1 pp.1.2))⁻¹ *
      presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk} 0 *
      evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}) (gW pp.1.1 pp.1.2) =
    (evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk})
        (gW pp.2.1 pp.2.2))⁻¹ *
      presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk} 0 *
      evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}) (gW pp.2.1 pp.2.2) := KernelFi22F.pairs_agree

end Certificates
