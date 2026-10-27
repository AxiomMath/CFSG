module

public import CFSG.GH74.KGroups.L33Inputs
import Certificates.Kernel.PermCent.KL33Glue

public section

namespace Certificates

open CFSG.GH74.KGroups in
theorem certificate5096 : ∀ τ ∈ L33.QA.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ x ∈ L33.QA.originalSubgroup,
    x * τ = τ * x → x ≠ 1 → Odd (orderOf x) →
    ∃ c ∈ L33.QP.originalSubgroup, c * τ = τ * c ∧ Even (orderOf (x * c * x⁻¹ * c⁻¹)) :=
  CFSG.Certificates.Kernel.PkCV.L33R.Glue.l33_oddCore

end Certificates
