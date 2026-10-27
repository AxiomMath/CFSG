module

public import Certificates.Data.GrSLitHeZStar
import Certificates.Kernel.CF23L34.HeZSGlue

public section

namespace Certificates

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  CFSG.ComponentClassification.GrSLit.HeGS Certificates.GrSLitHeZStar in
theorem certificate22704 :
    comp 8330 heZOuterTab heZOuterTab = idTab 8330 ∧ heZOuterTab ≠ idTab 8330 ∧
      heGSFix heZOuterTab = 346 ∧
      comp 8330 heZD1Tab heZD1Tab = idTab 8330 ∧ comp 8330 heZD2Tab heZD2Tab = idTab 8330 ∧
      heZD1Tab ≠ idTab 8330 ∧ heZD2Tab ≠ idTab 8330 ∧ heZD1Tab ≠ heZD2Tab ∧
      comp 8330 heZD1Tab heZD2Tab = comp 8330 heZD2Tab heZD1Tab ∧
      heZSylowOK = true ∧ heZTransOK = true ∧ heZFixOK = true ∧
      heGSFix heZUTab = 346 ∧ heGSFix heZT0UTab = 346 ∧
      comp 8330 heZT0UTab heZT0UTab = idTab 8330 ∧ heZT0UTab ≠ idTab 8330 :=
  CertificateChecks.KernelLC.HeZS.check22704

end Certificates
