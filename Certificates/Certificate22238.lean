module

public import Certificates.Data.GrSLitL34Sec5SWFusCheck
import Certificates.Kernel.L34W.TypesGlue
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real in
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso in
theorem certificate22238 : ∀ t < 64, ∀ i < 36, repInS.contains i = false →
    wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 → typeOf t i = 0 →
    ∀ z ∈ zInvs, fixKB (kbOfMask 1) t i z = true →
      ∃ x ∈ allM, fixKB (kbOfMask 1) t i x = true ∧ eqKB (kbOfMask 1) (mulM x x) z = true :=
  fun _ ht _ hi hS h2 h0 => KernelL34W.fieldSq_spec ht hi hS h2 h0

end Certificates
