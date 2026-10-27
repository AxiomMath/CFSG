module

public import CFSG.Sporadic.Recognition.RuMultiplierIndex
public import Certificates.Kernel.CosetJ.CJRu
public import Certificates.Kernel.CosetJ.Cover
public import CFSG.Certificates.Kernel.Orders.Ru.Rels
import CFSG.Certificates.Kernel.Orders.Ru.RelsBind
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.Sporadic.Presentation.RuExactInputs
import all CFSG.LieType.Multipliers.CoverWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

namespace CertificateChecks.KernelCosetJ.Ru

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.LieType.Multipliers

theorem w0_eq : CFSG.Sporadic.Presentation.Ru.Exact.W0.map encW = CFSG.KD.OrdRu.rels := by
  rw [← CFSG.KD.OrdRu.rels_eq, TauCeti.GroupPresentation.relatorLetters_def]
  rfl

theorem rels_eq : ruCover.map encW = CFSG.KBRoute.CJRu.rels := by
  rw [map_encW_coverWords, w0_eq]
  decide +kernel

theorem index_le : RuIndexK := by
  have h := CJRu.t1
  unfold CFSG.KBRoute.CJRu.T1.ok at h
  exact genSub_index_le_of_tableOk ruCover rels_eq h (by decide) CFSG.KBRoute.CJRu.top _ rfl

end CertificateChecks.KernelCosetJ.Ru

end
