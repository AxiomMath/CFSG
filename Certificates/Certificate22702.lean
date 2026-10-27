module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
import Certificates.Kernel.CF23L34.HeGSRGlue

public section

namespace Certificates

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  CFSG.ComponentClassification.GrSLit.HeGS in
theorem certificate22702 :
    heGSOK 10 heGSProg = true ∧ permChk 8330 heGSGTab = true ∧
      comp 8330 heGSGTab (heGen 0) = comp 8330 heGSVTab heGSGTab ∧
      (heGSRun 8330 heGSInit heGSProg)[133]!.1 = heGen 0 ∧
      (heGSRun 8330 heGSInit heGSProg)[134]!.1 = heGen 1 :=
  CertificateChecks.KernelLC.HeGSR.check22702

end Certificates
