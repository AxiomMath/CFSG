
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverInputs
import Certificates.Kernel.Multipliers.M12Cov

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12Cover in
theorem certificate291350 : Finite (CFSG.CosetTable.PG 2 m12Cover) ∧ Nat.card (CFSG.CosetTable.PG 2 m12Cover) ≤ 190080 ∧
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ m12Cover.map FreeGroup.mk}
      (FreeGroup.mk m12R3)) :=
  KernelM12Cov.bounds

end Certificates
