
module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck
import Certificates.Kernel.L34W.D1Glue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real in
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso in
theorem certificate22235 : ∀ kb ∈ kbList, kbFull kb = false →
    ∀ t < 64, ∀ i < 36, ∀ t' < 64, ∀ i' < 36, repInS.contains i = false →
      repInS.contains i' = false →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 →
      wordPerm (tg t') * repPerm i' * (wordPerm (tg t') * repPerm i') = 1 →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t') * repPerm i') =
        wordPerm (tg t') * repPerm i' * (wordPerm (tg t) * repPerm i) →
      ∃ a ∈ allM, ∃ b ∈ allM, eqKB kb b a = false ∧ fixKB kb t i a = true ∧
        fixKB kb t' i' a = true ∧ isInvKB kb a = true ∧ fixKB kb t i b = true ∧
        fixKB kb t' i' b = true ∧ isInvKB kb b = true := KernelL34W.d1_spec

end Certificates
