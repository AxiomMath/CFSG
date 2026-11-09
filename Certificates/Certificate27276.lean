module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
import Certificates.Kernel.HSStd.U43Z4Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 in
theorem certificate27276 : ∃ tPar yPar : Array (ℕ × ℕ), caseCheck dZ4 tPar yPar = true :=
  ⟨_, _, KernelHSStd.U43Z4.caseCheck_true⟩

end Certificates
