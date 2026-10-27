module

public import CFSG.Sporadic.Fi22.Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenInputs
import Certificates.Kernel.Fi22Gen.Glue

public section

namespace Certificates

open CertificateChecks

open scoped Pointwise in
theorem certificate25262 : 443520 ≤ Nat.card (MulAction.orbit
    (Subgroup.closure {x : CFSG.Sporadic.Fi22.J |
      x • (Finset.univ.filter fun y : Fin 3510 =>
        y.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted) =
        (Finset.univ.filter fun y : Fin 3510 =>
          y.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted) ∧ Odd (orderOf x)})
    (![190, 195, 526, 594, 752] : Fin 5 → Fin 3510)) := KernelFi22Gen.orbit_t0_ge

end Certificates
