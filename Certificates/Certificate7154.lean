module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Certificates.Kernel.A8Part.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate7154 : (∀ N : Subgroup (Equiv.Perm (Fin 8)), N ≤ alternatingGroup (Fin 8) →
      288 ∣ Nat.card N → N ≠ alternatingGroup (Fin 8) → ∃ S : Finset (Fin 8), S.card = 4 ∧
        ∀ g ∈ N, (∀ i, g i ∈ S ↔ i ∈ S) ∨ (∀ i, g i ∈ S ↔ i ∉ S)) ∧
    ∀ J : Subgroup (Equiv.Perm (Fin 8)), J ≤ alternatingGroup (Fin 8) → 64 ∣ Nat.card J →
      Nat.card J = 64 ∨ Nat.card J = 192 ∨ Nat.card J = 576 ∨ Nat.card J = 1344 ∨
        Nat.card J = 20160 :=
  ⟨KernelA8Part.Glue.part, KernelA8Part.Glue.two⟩

end Certificates
