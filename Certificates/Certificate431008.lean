module

import Certificates.Kernel.Co3Tw.PairGlue
public import CFSG.Sporadic.Schreier.Co3CertBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Co3 in
theorem certificate431008 : ∃ P : Subgroup (Equiv.Perm (Fin 276)),
    P ≤ co3P ∧ Nat.card P = 2187 ∧
      ∀ E : Subgroup (Equiv.Perm (Fin 276)), E ≤ P → (∀ x ∈ E, x ^ 3 = 1) →
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E = 9 →
        ∀ a ∈ co3P, ∀ b ∈ co3P, a ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))) →
          b ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))) →
          (∃ m, a ^ 3 ^ m = 1) → (∃ m, b ^ 3 ^ m = 1) → ∃ m, (a * b) ^ 3 ^ m = 1 :=
  ⟨KernelCo3Tw.P, KernelCo3Tw.P_le_co3P, KernelCo3Tw.card_P, KernelCo3Tw.closed_of_le_P⟩

end Certificates
