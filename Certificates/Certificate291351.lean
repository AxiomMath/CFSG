
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverInputs
import Certificates.Kernel.Multipliers.J2Cov

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2Cover in
theorem certificate291351 : Finite (CFSG.CosetTable.PG 2 j2Cover) ∧ Nat.card (CFSG.CosetTable.PG 2 j2Cover) ≤ 1209600 ∧
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ j2Cover.map FreeGroup.mk}
      (FreeGroup.mk j2R3)) :=
  KernelJ2Cov.bounds

end Certificates
