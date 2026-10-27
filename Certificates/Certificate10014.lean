module

public import CFSG.LieType.Multipliers.U43Kernel
import Certificates.Kernel.Multipliers.U43Lower

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.LieType.Multipliers.U43 in
theorem certificate10014 : ∃ (E : Type) (_ : Group E) (ψ : PG 2 coverWs →* E)
    (τ : Multiplicative (ZMod 12 × ZMod 3) →* E), Function.Injective τ ∧
      ψ (zk 5) = τ (Multiplicative.ofAdd (4, 0)) ∧ ψ (zk 6) = τ (Multiplicative.ofAdd (9, 1)) := KernelU43.kernel_model

end Certificates
