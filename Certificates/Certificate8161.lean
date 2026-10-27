module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Census.NC2.McLFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate8161 : ∃ (t g x : NativeSporadic.McL) (S : Subgroup NativeSporadic.McL),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 7 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := KernelNC2.McL.facts

end Certificates
