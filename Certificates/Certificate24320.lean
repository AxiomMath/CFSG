module

public import CFSG.Sporadic.Recognition.ONMultiplierTables
import Certificates.Kernel.Sporadic.ONC.CheckGlue
import Certificates.Kernel.TwistDce3.ON.Bound

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier in
theorem certificate24320 :
    (Subgroup.closure (Set.range onGF) = ⊤ ∧
      (∀ r ∈ onRels, FreeGroup.lift onGF (FreeGroup.mk r) = 1) ∧
      (∀ i, FreeGroup.lift onGF (FreeGroup.mk (onCommWord i)) = onGF i)) ∧
    ((genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk}
        (subsetOf 4 [0, 1, 2])).index ≤ 245520) ∧
    (Finite (PG 4 onCover) ∧ Nat.card (PG 4 onCover) ≤ 460815505920) :=
  ⟨⟨KernelSpor.ONC.closure_onGF, KernelSpor.ONC.lift_onGF_rels, KernelSpor.ONC.lift_onGF_commWord⟩,
    CFSG.KD.ONDce3.index_genSub_onCover_le, CFSG.KD.ONDce3.card_onCover_le⟩

end Certificates
