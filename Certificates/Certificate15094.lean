module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalCo1HoltFreeTwoCInputs
import Certificates.Kernel.Co1B.C15094

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.ComponentClassification.RankTwoExceptional.HoltFree in
theorem certificate15094 : holtFreeOrderCheck = true
    ∧ holtFreeFixCheck = true
    ∧ xFixCount certVecs holtFreeA = 2280
    ∧ xFixCount certVecs holtFreeB = 264
    ∧ xFixCount certVecs (mul holtFreeB iotaCRows) = 264
    ∧ xFixCount certVecs holtFreeF = 2280
    ∧ xFixCount certVecs (mul holtFreeA holtFreeF) = 2280 := KernelCo1B.C15094.c15094

end Certificates
