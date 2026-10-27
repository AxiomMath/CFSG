module

public import CFSG.Sporadic.Fi23.Setup
import Certificates.Kernel.CentGenK.Fi23Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23 in
theorem certificate17254 : 
    ∃ e f s₁ s₂ : GL (Fin 253) (ZMod 3), Subgroup.closure {s₁, s₂} = CFSG.Sporadic.Fi23.J ∧ e ∈ CFSG.Sporadic.Fi23.J ∧ f ∈ CFSG.Sporadic.Fi23.J ∧
      e ^ 5 = 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧ e ≠ 1 ∧ (∀ k < 5, f ≠ e ^ k) ∧
      s₁ * e = e * s₁ ∧ s₂ * f = f * s₂ :=
  KernelCentGenK.Fi23.fi23_cg_exists

end Certificates
