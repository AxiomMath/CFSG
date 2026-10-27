module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverInputs
public import CFSG.Sporadic.Recognition.ONMultiplierTables
import Certificates.Kernel.Sporadic.ONC.TauGlue
import Certificates.Kernel.ONCover.Dce.Bound

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover in
theorem certificate291371 :
    (∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1) ∧
    (Finite (PG 4 mainWs) ∧ Nat.card (PG 4 mainWs) ≤ 1382446517760) ∧
    (Finite (PG 4 hatS) ∧ Nat.card (PG 4 hatS) ≤ 5630688) ∧
    (∃ (Ω : Type) (ψ : PG 4 hatS →* (Equiv.Perm Ω)ᵐᵒᵖ) (b : Ω), ∀ u ℓ, (u, ℓ) ∈ hatWords → 0 < ℓ →
      Function.minimalPeriod
        (ψ (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
          (FreeGroup.mk u))).unop b = ℓ) :=
  ⟨KernelSpor.ONC.lift_onGF_tauWords, CFSG.KD.ONCoverDce3.card_mainWs_le,
    KernelONCover.card_hatS_le, KernelONCover.hat_periods⟩

end Certificates
