module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ECertInputs
import Certificates.Kernel.L34Cov.Field22234

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22234 :
    (∀ s ∈ fieldZSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    r3Idx.all (fun k => comp 42 (wordTab (tg k)) r₃T == comp 42 r₃T (wordTab (tg k))) = true := KernelL34Cov.facts22234

end Certificates
