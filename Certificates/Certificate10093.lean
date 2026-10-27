module

public import CFSG.YGroups.Defs
import Certificates.Kernel.YChain.Chain

public section

namespace Certificates

open CertificateChecks.KernelYChain

open CFSG.YGroups in
theorem certificate10093 :
    (Finite (YGroup 0 0 0) ∧ Nat.card (YGroup 0 0 0) ≤ 2)
    ∧ (Finite (YGroup 1 0 0) ∧ Nat.card (YGroup 1 0 0) ≤ 3 * 2)
    ∧ (Finite (YGroup 1 1 0) ∧ Nat.card (YGroup 1 1 0) ≤ 4 * (3 * 2))
    ∧ (Finite (YGroup 1 1 1) ∧ Nat.card (YGroup 1 1 1) ≤ 8 * (4 * (3 * 2)))
    ∧ (Finite (YGroup 2 1 1) ∧ Nat.card (YGroup 2 1 1) ≤ 10 * (8 * (4 * (3 * 2))))
    ∧ (Finite (YGroup 2 2 1) ∧ Nat.card (YGroup 2 2 1) ≤ 51840)
    ∧ (Finite (YGroup 2 2 2) ∧ Nat.card (YGroup 2 2 2) ≤ 12597120)
    ∧ (Finite (YGroup 3 2 2) ∧ Nat.card (YGroup 3 2 2) ≤ 9170703360)
    ∧ (Finite (YGroup 3 3 2) ∧ Nat.card (YGroup 3 3 2) ≤ 258247006617600)
    ∧ (Finite (YGroup 4 3 2) ∧ Nat.card (YGroup 4 3 2) ≤ 8178940946586009600) :=
  ⟨y000, y100, y110, y111, y211, y221, y222, y322, y332, y432⟩

end Certificates
