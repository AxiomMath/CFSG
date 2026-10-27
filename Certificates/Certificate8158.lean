module

public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.Census.NC2.HNFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint in
theorem certificate8158 : ∃ (t g x : NativeSporadic.HN) (S : Subgroup NativeSporadic.HN),
    orderOf t = 2 ∧ S ≤ Subgroup.centralizer {t} ∧ Nat.card S = 2 ^ 11 ∧
    g ∈ Subgroup.centralizer {t} ∧ x ∈ Subgroup.centralizer {t} ∧ x ≠ 1 ∧ Odd (orderOf x) ∧
    (∀ s ∈ S ⊓ S.map (MulAut.conj g).toMonoidHom, x * s = s * x) ∧
    11 ∣ Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.HN)) := KernelNC2.HN.facts

end Certificates
