module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHe36CertInputs
import Certificates.Kernel.LocalComp.HeGS36Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  CFSG.ComponentClassification.GrSLit.HeGS in
theorem certificate22703 :
    comp 8330 heGS36CTab (heGSKTab (heDWords.getD 1 [])) = comp 8330 heT1Arr heGS36CTab ∧
      permChk 8330 heGS36CTab = true ∧
      (∀ p < 4, hfCTab (heGS36D p 0 ++ heGS36D p 1) = idTab 8330 ∧
        hfCTab (heGS36D p 2 ++ heGS36D p 3) = idTab 8330 ∧
        hfCTab (heGS36Word p) = heGS36Target p) ∧
      comp 8330 (heGSKTab (heDWords.getD 1 [])) heGSInit[5]!.1 ≠
        comp 8330 heGSInit[5]!.1 (heGSKTab (heDWords.getD 1 [])) ∧
      comp 8330 (heGSKTab (heGSComm2 heGSUComm)) (heGSKTab (heGSComm2 heGSUComm)) = idTab 8330 := KernelLC.HeGS36.check

end Certificates

end
