module

public import Certificates.Data.NPL587
public import Mathlib.SetTheory.Cardinal.Finite
import Certificates.Kernel.NPL587.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate587001 :
    Nat.card (Subgroup.closure
      {g : Equiv.Perm (Fin 8) | g ∈ CFSG.Quasithin.H13.NPL.S0gens ()}) = 64 ∧
    ∀ σ : Equiv.Perm (Fin 8), σ ≠ 1 → (σ ^ 5 = 1 ∨ σ ^ 7 = 1) →
      448 < Nat.card (Subgroup.closure (insert σ (↑(Subgroup.closure
        {g : Equiv.Perm (Fin 8) | g ∈ CFSG.Quasithin.H13.NPL.S0gens ()}) :
          Set (Equiv.Perm (Fin 8))))) :=
  KernelNPL587.facts

end Certificates
