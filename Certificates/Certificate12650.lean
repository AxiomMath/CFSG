
module

public import CFSG.LieType.Multipliers.U43Action
import Certificates.Kernel.U43Alpha.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.U43 in
theorem certificate12650 : ∀ b : CFSG.LieType.Multipliers.U43.X₀, orderOf b = 3 → ∀ τ : MulAut CFSG.LieType.Multipliers.U43.X₀, τ ^ 2 = 1 →
    τ ∉ (MulAut.conj : CFSG.LieType.Multipliers.U43.X₀ →* MulAut CFSG.LieType.Multipliers.U43.X₀).range →
      ¬ ∀ c ∈ Subgroup.centralizer ({b} : Set CFSG.LieType.Multipliers.U43.X₀), τ c = c :=
  KernelU43Alpha.outer_not_fix_kernel

end Certificates
