module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFixInputs
import Certificates.Kernel.TwoDFix.C15082

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15082 : CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.rowsCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.qCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.alphaCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.pauliCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.commCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.u7Check = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.betaCheck = true ∧
    CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix.sCheck = true := KernelTwoDFix.c15082

end Certificates
