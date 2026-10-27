module

public import CFSG.YGroups.Defs
import Certificates.Kernel.YChain.ChainA

public section

namespace Certificates

open CertificateChecks.KernelYChain

open CFSG.YGroups in
theorem certificate3174 : (Finite (YGroup 2 1 0) ∧ Nat.card (YGroup 2 1 0) ≤ 120)
    ∧ (Finite (YGroup 2 2 0) ∧ Nat.card (YGroup 2 2 0) ≤ 720)
    ∧ (Finite (YGroup 3 2 0) ∧ Nat.card (YGroup 3 2 0) ≤ 5040)
    ∧ (Finite (YGroup 3 3 0) ∧ Nat.card (YGroup 3 3 0) ≤ 40320)
    ∧ (Finite (YGroup 4 3 0) ∧ Nat.card (YGroup 4 3 0) ≤ 362880)
    ∧ (Finite (YGroup 4 4 0) ∧ Nat.card (YGroup 4 4 0) ≤ 3628800) :=
  ⟨y210, y220, y320, y330, y430, y440⟩

end Certificates
