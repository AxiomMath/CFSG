module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
import Certificates.Kernel.CF23L34.HeGSLGlue

public section

namespace Certificates

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  CFSG.ComponentClassification.GrSLit.HeGS in
theorem certificate22701 :
    (∀ j < 9, comp 8330 (heInnerC0 j) (heInnerC0 j) = idTab 8330) ∧
      heGSKTab (heGSComm2 heGST0Comm) = heGen 0 ∧
      fixesOK 105 (heGen 0) heOmega0 = true ∧
      fixesOK 105 (heGSKTab (heGSComm2 heGSUComm)) heOmega0 = true ∧
      heGSKTab (heGSComm2 heGSUComm) ≠ idTab 8330 ∧
      heGSKTab (heGSComm2 heGSUComm) ≠ heGen 0 ∧
      comp 8330 heGSVTab heGSVTab = idTab 8330 ∧ heGSVTab ≠ idTab 8330 ∧
      heGSFix heGSVTab = 346 ∧ heGSFix (heGSKTab (heDWords.getD 1 [])) ≠ 346 ∧
      heGSFix (heGSKTab (heGSComm2 heGSUComm ++ heDWords.getD 1 [])) ≠ 346 ∧
      heGSFix (heGSKTab (0 :: (heGSComm2 heGSUComm ++ heDWords.getD 1 []))) ≠ 346 ∧
      comp 8330 (heGSKTab (heDWords.getD 0 [])) heGSVTab ≠
        comp 8330 heGSVTab (heGSKTab (heDWords.getD 0 [])) ∧
      comp 8330 (heGSKTab (heDWords.getD 0 [])) (heGSKTab (heDWords.getD 1 [])) ≠
        comp 8330 (heGSKTab (heDWords.getD 1 [])) (heGSKTab (heDWords.getD 0 [])) ∧
      ∀ l ∈ [2, 3, 4, 5, 6, 7, 8, 9], comp 105 (heGSDRep l) (heGSDRep l) ≠ idTab 105 :=
  CertificateChecks.KernelLC.HeGSL.check22701

end Certificates
