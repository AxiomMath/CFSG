module

public import CFSG.Sporadic.J4.QTRankProof
import Certificates.Kernel.J4NP.Elab7851Asm

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem certificate7851 : ∀ A : Subgroup CFSG.Sporadic.J4.J, A ≤ P0 → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
    ¬ A ≤ Eg uJ 11 → Nat.card ↥A ≤ 2 ^ 10 := KernelJ4NP.star7851

end Certificates
