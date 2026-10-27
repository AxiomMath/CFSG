
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
import Certificates.Kernel.CU43Aut.ModelFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate26010 : (permCheck = true) ∧ (normCheck = true) ∧ (relCheck = true) ∧ (CFSG.EvenSporadicStandard.M24Std.CU43.cosetCheck = true) ∧
      (multCheck = true) ∧ (CFSG.EvenSporadicStandard.M24Std.CU43.repCheck = true) := KernelCU43Aut.facts26010

end Certificates
