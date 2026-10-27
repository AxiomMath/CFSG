module

public import CFSG.LieType.Multipliers.U62SylowInputs
import Certificates.Kernel.Misc.Coset.C10018
public import CFSG.Certificates.WordSubgroup
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.LieType.Multipliers.U62 CFSG.LieType.Multipliers in
theorem certificate10018 :
    (Finite (PG 2 sylowRels) ∧ Nat.card (PG 2 sylowRels) ≤ 81)
    ∧ (∀ u ∈ sylowRels.map (substWord sylowWordsAB),
      PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverAB.map FreeGroup.mk} (FreeGroup.mk u) = 1) :=
  ⟨KernelMiscCoset.C10018.sylow_card_le, KernelMiscCoset.C10018.relations⟩

end Certificates
