module

public import Certificates.Data.TwE6WKMatrix
import Certificates.Kernel.E6WK.Assembly

public section

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TwE6RootKill in
theorem certificate830101 : ∀ w : WeylGroup TwistTag.E6.tag,
    (∃ i, IsRoot TwistTag.E6.tag (wkMatrix w i)) ∨ wkMatrix w = 0 ∨
      ∃ R C : Fin 3 → Fin TwistTag.E6.tag.rank,
        ((wkMatrix w).submatrix R C).det ∈ ({1, -1, 2, -2} : Finset ℤ) :=
  CertificateChecks.KernelE6WK.e6wk_trichotomy

end Certificates
