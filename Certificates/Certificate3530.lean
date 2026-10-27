module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData
import Certificates.Kernel.OmegaEight.CPrimeEval

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.CPrime in
theorem certificate3530 : (reflRowsCheck .plus = true)
    ∧ (reflRowsCheck .minus = true)
    ∧ (reflQfCheck .plus = true)
    ∧ (reflQfCheck .minus = true)
    ∧ (sigmaCheck .plus = true)
    ∧ (sigmaCheck .minus = true)
    ∧ (transNCheck .plus = true)
    ∧ (transNCheck .minus = true)
    ∧ (sumCheck .plus = true)
    ∧ (sumCheck .minus = true)
    ∧ (order3Check = true) := KernelO8.cert3530

end Certificates
