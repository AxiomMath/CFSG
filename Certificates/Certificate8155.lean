module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Census.NC2.Co3Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate8155 : ∃ (t g x : NativeSporadic.Co3) (S : Subgroup NativeSporadic.Co3),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 10 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := KernelNC2.Co3.facts

end Certificates
