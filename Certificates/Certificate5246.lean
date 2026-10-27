module

import Certificates.Kernel.Ivk8J2.Final
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate5246 : ∀ S W : Subgroup (Equiv.Perm (Fin 315)), S ≤ CFSG.Sporadic.Schreier.j2P →
    W ≤ CFSG.Sporadic.Schreier.j2P → Nat.card S = 2 ^ 7 → IsPGroup 3 W →
    S ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 315))) → W = ⊥ := KernelIvk8J2.noThree_j2P

end Certificates
