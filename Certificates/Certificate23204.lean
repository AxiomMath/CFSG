module

public import Certificates.Data.FooteLitL34FUCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs
import Certificates.Kernel.L34FU.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.GrSLit.L34Facts in
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.TBLit.L34FU in
theorem certificate23204 : (∀ ρ ∈ R, ρ ^ 16 = 1 → ρ ^ 8 = 1) ∧ g₄ * r₄ = r₄ * g₄ ∧
    ∀ t < 64, ∀ i < 36,
      wordPerm (tg t) * CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i * (wordPerm (tg t) * CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i) = 1 →
      wordPerm (tg t) * CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i * CFSG.ComponentClassification.PSL3Four.r₂ = CFSG.ComponentClassification.PSL3Four.r₂ * (wordPerm (tg t) * CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i) →
      (∃ c ∈ R, wordPerm (tg t) * CFSG.ComponentClassification.GrSLit.L34Facts.Real.repPerm i = c * r₄ * c⁻¹) →
      ∃ x ∈ allM, betaRepM 1 x = x ∧ pow4X (mulM x (betaYM t i x)) = (0, 2, 0) := KernelL34FU.facts23204

end Certificates
