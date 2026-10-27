module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsTransversalCheckInputs
import Certificates.Kernel.M12Cover.T25C
import Certificates.Kernel.M12Cover.T25TR

public section

namespace Certificates

open CertificateChecks.KernelM12T in
open CFSG.ComponentClassification.M12Cover.InternalSylow in
theorem certificate10025 :
    (rCodeCheck = true)
    ∧ (cosetCheck = true)
    ∧ (decompCheck = true)
    ∧ (betaCheck = true)
    ∧ (quotCheck = true)
    ∧ (transferCheck = true)
    ∧ (lambdaCheck = true) :=
  ⟨rCodeC, cosetC, decompC, betaC, quotC, transC, lamC⟩

end Certificates
