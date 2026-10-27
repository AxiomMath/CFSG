module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsNonsplitDataInputs
import Certificates.Kernel.Misc.Coset.C3144

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMiscCoset.C3144 in
open CFSG.EvenSmallLie.UnitarySix CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62
  CFSG.CosetTable CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi22.Native in
theorem certificate3144 : 
      (u62W (expand nsE) ∈ Subgroup.closure {g | g ∈ aGens} ∧
        (∀ k ∈ [u62W (expand nsN₁), u62W (expand nsN₂)], ∀ a ∈ aGens,
          k * a * k⁻¹ ∈ Subgroup.closure {g | g ∈ aGens}) ∧
        t46FixAll (wordT 693 t46Gen (expand nsC₁)) = true ∧
        t46FixAll (wordT 693 t46Gen (expand nsC₂)) = true)
    ∧ ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
      ∀ u ∈ exclWords nsC₁ (0, 1, 0) ++ exclWords nsC₂ (0, 0, 1),
        ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 := by
  exact ⟨⟨nsE_mem, nsN_conj, comm_fix.1, comm_fix.2⟩, cover⟩

end Certificates
