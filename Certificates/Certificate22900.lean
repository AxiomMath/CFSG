module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4WitCertInputs
import Certificates.Kernel.L34Cov.Wit22900

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.L34 CFSG.CosetTable CFSG.ComponentClassification.GrSLit.GrS4 in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22900 :
    (∀ s ∈ witSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    syl3WitOK = true := KernelL34Cov.facts22900

end Certificates
