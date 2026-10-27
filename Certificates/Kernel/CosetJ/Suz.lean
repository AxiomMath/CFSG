module

public import CFSG.Sporadic.Recognition.SuzMultiplierInputs
public import Certificates.Kernel.CosetJ.CJSuz0
public import Certificates.Kernel.CosetJ.CJSuz1
public import Certificates.Kernel.CosetJ.Cover
public import Certificates.Kernel.Bounds.Suz.Binding
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all CFSG.Sporadic.Presentation.SuzInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CentralizerRelations
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki

public section

namespace CertificateChecks.KernelCosetJ.Suz

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Suz

instance : NeZero gcS := ⟨by decide⟩

theorem R0_eq : R0 = decodeW gcS CFSG.KBRoute.Suz.rels := by
  refine eq_decodeW ?_
  rw [← CFSG.KBRoute.Suz.rels_eq, TauCeti.GroupPresentation.relatorLetters_def]
  rfl

theorem suzCover_eq : suzCover = coverWords (decodeW gcS CFSG.KBRoute.Suz.rels) suzCommWord := by
  rw [← R0_eq]

theorem rels₀ : suzCover.map encW = CFSG.KBRoute.CJSuz0.rels := by
  rw [suzCover_eq]
  decide +kernel

theorem rels₁ : suzCover1.map encW = CFSG.KBRoute.CJSuz1.rels := by
  rw [show suzCover1 = restrictWords (subsetOf gcS [0, 1, 2, 3, 4, 6]) suzCover from rfl,
    suzCover_eq]
  decide +kernel

theorem index₀ :
    (genSub {r : FreeGroup (Fin gcS) | r ∈ suzCover.map FreeGroup.mk}
      (subsetOf gcS [0, 1, 2, 3, 4, 6])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin gcS) | r ∈ suzCover.map FreeGroup.mk}
      (subsetOf gcS [0, 1, 2, 3, 4, 6])).index ≤ 5346 := by
  have h := CJSuz0.t1
  unfold CFSG.KBRoute.CJSuz0.T1.ok at h
  exact genSub_index_le_of_tableOk suzCover rels₀ h (by decide) CFSG.KBRoute.CJSuz0.top _ rfl

theorem index₁ :
    (genSub {r : FreeGroup (Fin (subsetOf gcS [0, 1, 2, 3, 4, 6]).length) |
        r ∈ suzCover1.map FreeGroup.mk} (subsetOf _ [0, 1, 2, 3, 4])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin (subsetOf gcS [0, 1, 2, 3, 4, 6]).length) |
        r ∈ suzCover1.map FreeGroup.mk} (subsetOf _ [0, 1, 2, 3, 4])).index ≤ 416 := by
  have h := CJSuz1.t1
  unfold CFSG.KBRoute.CJSuz1.T1.ok at h
  exact genSub_index_le_of_tableOk suzCover1 rels₁ h (by decide) CFSG.KBRoute.CJSuz1.top _ rfl

end CertificateChecks.KernelCosetJ.Suz

end
