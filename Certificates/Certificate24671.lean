module

public import CFSG.Sporadic.Fi22.Transpositions
import Certificates.Kernel.Fi22Flag.Sound

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22 in
theorem certificate24671 : ∀ (S : Sylow 2 J),
    Nat.card {x : J // x ∈ D ∧ x ∈ (S : Subgroup J)} ≤ 22 :=
  by
    intro S
    exact KernelFi22Flag.card_D_sylow_le S

end Certificates

end

end
