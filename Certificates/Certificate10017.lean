module

public import CFSG.LieType.Multipliers.U62KernelInputs
import Certificates.Kernel.Misc.Coset.C10017
public import Certificates.Certificate1002

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.CosetTable in
theorem certificate10017 :
    ((genSub {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk} (subsetOf 5 [0, 1, 2, 3])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 5) | r ∈ coverWs.map FreeGroup.mk}
        (subsetOf 5 [0, 1, 2, 3])).index ≤ 8064)
    ∧ ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
      (∀ u ∈ fixWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) = 1) ∧
        ∀ u ∈ moveWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 :=
  ⟨KernelMiscCoset.C10017.index, KernelMiscCoset.C10017.hom⟩

end Certificates
