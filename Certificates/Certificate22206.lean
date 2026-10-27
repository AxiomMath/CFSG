module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2CertInputs
import Certificates.Kernel.L34Cov.Facts22206

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.L34 CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22206 :
    (∀ s ∈ cover2Specs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    commData2.all (fun d => (d.2.2.1 == 0 || d.2.2.1 == 2) && (d.2.2.2.1 == 0 || d.2.2.2.1 == 2)) =
      true ∧
    transOK = true ∧ cceOK = true := KernelL34Cov.facts22206

end Certificates
