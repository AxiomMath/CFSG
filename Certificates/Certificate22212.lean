module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLiftCertInputs
import Certificates.Kernel.L34Cov.Lift22212

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22212 :
    (∀ s ∈ liftSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    liftNormOK = true := KernelL34Cov.facts22212

end Certificates
