module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigCases
import Certificates.Kernel.HSStd.U43VbGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HSStd.U43 in
theorem certificate27277 : ∃ tPar yPar : Array (ℕ × ℕ), caseCheck dVb tPar yPar = true :=
  ⟨_, _, KernelHSStd.U43Vb.caseCheck_true⟩

end Certificates
