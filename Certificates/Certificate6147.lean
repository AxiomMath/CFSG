module

public import CFSG.LocalAnalysis.OddStandard.ONanIdCertInputs
import Certificates.Kernel.L34Cov.Id6147

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ONanRec.IdCert CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate6147 :
    sigmaOK = true ∧ centOK = true ∧
    ∀ s ∈ idSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2)) := KernelL34Cov.facts6147

end Certificates
