module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3LineTests
import Certificates.Kernel.AS81.Facts

public section

open CFSG

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15064 : CFSG.ComponentClassification.AS81.MinusLines.lineCheck = true ∧
    CFSG.ComponentClassification.AS81.MinusLines.lineGensCheck = true ∧
    CFSG.ComponentClassification.AS81.MinusLines.lineTransCheck = true ∧
    CFSG.ComponentClassification.AS81.MinusLines.lineH0Check = true ∧
    CFSG.ComponentClassification.AS81.MinusLines.lineMergeCheck = true :=
  ⟨KernelAS81.line_check, KernelAS81.lineGens_check, KernelAS81.lineTrans_check,
    KernelAS81.lineH0_check, KernelAS81.lineMerge_check⟩

end Certificates
