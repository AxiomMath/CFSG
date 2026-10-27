module

public import CFSG.LocalAnalysis.OddStandard.ONanIdCMInputs
import Certificates.Kernel.L34Cov.CM6148

public section

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.ONanRec.IdCM CFSG.LieType.Multipliers.L34 CFSG.CosetTable in
open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate6148 :
    (∀ d ∈ relData, (nfOf d.1.toWord).2 = false) ∧ (nfOf invA).2 = false ∧
    (nfOf invB).2 = false ∧ (nfOf invU).2 = true ∧
    ∀ s ∈ cmSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2)) := KernelL34Cov.facts6148

end Certificates
