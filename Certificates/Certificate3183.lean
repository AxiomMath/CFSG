module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerLeviInputs
import Certificates.Kernel.TwoE6.InnerLevi

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6.Stroth23Inner CFSG.Fischer CFSG.LieType.Universal.Unitary Matrix in
open CFSG.Monster.B.Classical.UnitarySix in
theorem certificate3183 : (Ymat.det = 1)
    ∧ ((Ymat.map bar)ᵀ * antidiag 6 * Ymat = antidiag 6)
    ∧ (Ymat * (1 + Matrix.single 2 3 1) = (1 + Matrix.single 2 3 1) * Ymat)
    ∧ ((Ymat * Ymat * Ymat).trace ≠ bar (Ymat * Ymat * Ymat).trace) := KernelTwoE6.cert3183

end Certificates
