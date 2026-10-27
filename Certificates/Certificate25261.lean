module

public import CFSG.Sporadic.Fi22.Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenInputs
import Certificates.Kernel.Fi22Gen.Glue

public section

namespace Certificates

open CertificateChecks

open scoped Pointwise in
theorem certificate25261 : 142155 ≤ Nat.card (MulAction.orbit CFSG.Sporadic.Fi22.J
    (Finset.univ.filter fun x : Fin 3510 =>
      x.val ∈ CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.genUSorted)) := KernelFi22Gen.orbit_U_ge

end Certificates
