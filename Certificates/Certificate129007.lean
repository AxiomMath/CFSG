module

public import CFSG.Sporadic.SmallOddCore.J3Data
import Certificates.Kernel.J3Rank.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate129007 : ∀ B : Subgroup (Equiv.Perm (Fin 6156)), B ≤ CFSG.Sporadic.SmallOddCore.j3S →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 31 :=
  fun _ hBS hcomm hsq => KernelJ3Rank.j3S_elemAb_card_le hBS hcomm hsq

end Certificates
