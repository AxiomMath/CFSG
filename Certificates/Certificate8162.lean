module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Census.NC2.ONFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate8162 : ∃ (t g x : NativeSporadic.ON) (S : Subgroup NativeSporadic.ON),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 9 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := KernelNC2.ON.facts

end Certificates
