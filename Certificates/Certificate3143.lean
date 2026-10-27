module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionDataInputs
import Certificates.Kernel.Misc.Coset.C3143

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62
  CFSG.CosetTable in
theorem certificate3143 : (deltaRelCheck = true)
    ∧ ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
      ∀ u ∈ obsMoveWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 :=
  ⟨KernelMiscCoset.C3143.deltaRel, KernelMiscCoset.C3143.obs⟩

end Certificates
