module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Census.NC2.LyFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate8159 : ∃ (t g x : NativeSporadic.Ly) (S : Subgroup NativeSporadic.Ly),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 8 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    ∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x := KernelNC2.Ly.facts

end Certificates
