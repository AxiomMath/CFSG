module

public import Certificates.Data.GrSLitL34Sec5SWFusCheck
import Certificates.Kernel.L34W.TwoGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts.Real in
open CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso in
theorem certificate22239 : ∀ kb ∈ kbList,
    ∃ x₁ ∈ allM, ∃ x₂ ∈ allM, ∃ x₃ ∈ allM, ∃ x₄ ∈ allM,
      isInvKB kb x₁ = true ∧ isInvKB kb x₂ = true ∧ isInvKB kb x₃ = true ∧
      isInvKB kb x₄ = true ∧ eqKB kb x₂ x₁ = false ∧ commKB kb x₁ x₂ = true ∧
      commKB kb x₃ x₁ = true ∧ commKB kb x₃ x₂ = true ∧ commKB kb x₄ x₁ = true ∧
      commKB kb x₄ x₂ = true ∧ commKB kb x₃ x₄ = false := KernelL34W.two_spec

end Certificates
