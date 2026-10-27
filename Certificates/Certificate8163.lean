module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Census.NC2.SuzFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate8163 : ∃ (t g x : NativeSporadic.Suz) (S : Subgroup NativeSporadic.Suz),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 9 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
    7 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.Suz)) := KernelNC2.Suz.facts

end Certificates
