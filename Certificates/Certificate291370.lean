module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3CoverGen
import Certificates.Kernel.J3Cover.RelsGlue
import Certificates.Kernel.J3Cover.TablesGlue
import Certificates.Kernel.J3Cover.ModelGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J3Cover in
theorem certificate291370 :
    (∀ w ∈ checkWords, FreeGroup.lift gen (FreeGroup.mk w) = 1) ∧
    (Finite (PG 3 coverS) ∧ Nat.card (PG 3 coverS) ≤ 150698880) ∧
    3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ coverS.map FreeGroup.mk}
      (FreeGroup.mk walkWord)) :=
  ⟨fun _ hw => KernelJ3Cover.lift_checkWords_eq_one hw, KernelJ3Cover.card_coverS_le,
    KernelJ3Cover.three_dvd_orderOf_walkWord⟩

end Certificates
