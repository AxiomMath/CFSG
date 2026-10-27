module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
import Certificates.Kernel.J2Cover.M22Grp
import Certificates.Kernel.J2Cover.M22Lam
import Certificates.Kernel.J2Cover.EncM22

public section

namespace Certificates

open CertificateChecks.KernelJ2Cover in
open CFSG.ComponentClassification.J2Cover.Models in
theorem certificate10022 :
    (sCheck = true)
    ∧ (cosetCheck = true)
    ∧ (sDecompCheck = true)
    ∧ (cocycleCheck = true)
    ∧ (transferCheck = true)
    ∧ (involCheck = true)
    ∧ (outerCheck = true)
    ∧ (lambdaCheck = true)
    ∧ (groupCheck = true) :=
  ⟨sC, csCE, sdCE, cocyC, trC, invC, outCE, lamC22, grpC⟩

end Certificates
