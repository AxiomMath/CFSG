module

public import CFSG.Sporadic.Recognition.M22MultiplierInputs
import Certificates.Kernel.Multipliers.M22Cov

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.M22Multiplier in
theorem certificate24094 : Finite (PG 2 m22Cover) ∧ Nat.card (PG 2 m22Cover) ≤ 5322240 ∧
    12 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}
      (FreeGroup.mk m22B11)) :=
  KernelM22Cov.bounds

end Certificates
