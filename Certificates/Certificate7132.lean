module

import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.End

public section

open Equiv Equiv.Perm

namespace CertificateChecks.Batch7132

open Equiv Equiv.Perm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem centralizer_check :
    ∀ σ : Perm (Fin 7),
      σ * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) =
          (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) * σ →
        σ * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * σ →
          σ = 1 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 4 5 ∨
            σ = swap 0 2 * swap 1 3 * swap 4 5 := by
  decide +kernel

end CertificateChecks.Batch7132

namespace Certificates

open CertificateChecks

open Equiv Equiv.Perm in
theorem certificate7132 :
    ∀ σ : Perm (Fin 7),
      σ * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) =
          (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) * σ →
        σ * (swap 0 1 * swap 2 3) = (swap 0 1 * swap 2 3) * σ →
          σ = 1 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 4 5 ∨ σ = swap 0 2 * swap 1 3 * swap 4 5 :=
  CertificateChecks.Batch7132.centralizer_check

end Certificates
