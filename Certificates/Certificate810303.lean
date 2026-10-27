module

public import CFSG.Sporadic.ThI301.Inputs
import Certificates.Kernel.ThI301.Glue

public section

namespace Certificates

open CFSG.Sporadic.ThI301 in
theorem certificate810303 : ∀ X : Equiv.Perm (Fin 9), X * X = 1 → X ≠ 1 →
    ∃ Y ∈ a9Conj, X * (Y * X * Y⁻¹) ≠ Y * X * Y⁻¹ * X :=
  CertificateChecks.ThI301K.th_check

end Certificates
