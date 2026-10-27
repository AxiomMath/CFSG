module

import Certificates.Kernel.Sporadic.Fi22.AutH25290G
public import CFSG.Monster.B.Fischer.Fi22OuterBase
public import CFSG.Monster.B.Fischer.PinnedChainBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer in
theorem certificate25290 : ∃ N : Subgroup (Equiv.Perm (Fin 3510)), N ≤ fi22P ∧ (∀ v ∈ N, v * v = 1) ∧
    (∀ v ∈ N, ∀ w ∈ N, v * w = w * v) ∧ Nat.card N = 2 ^ 10 ∧
    (∀ v ∈ N, v 0 = 0 → v = 1) ∧
    (∀ q : Fin 3510, (∀ v ∈ N, v q = q → v = 1) → ∃ v ∈ N, v 0 = q) ∧
    fi22P ≤ Subgroup.closure ((fun v => v * fi22OuterZ * v⁻¹) '' (N : Set (Equiv.Perm (Fin 3510)))) := KernelSpor.AH25.facts

end Certificates
