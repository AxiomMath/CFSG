
module

public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Presentation.RuExact
public import Certificates.Data.CFSGNative.Bridge.SurjD
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.RuExactInputs
public import Certificates.Data.CFSGNative.Ru.Data
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.Ru

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native TauCeti

private theorem presentation_eq : SporadicName.Ru.presentation = Sporadic.ruPresentation := rfl

theorem generatorCount_eq : Sporadic.ruPresentation.generatorCount = ruSpec.m := by
  simp [GroupPresentation.generatorCount, ruSpec]

theorem relatorLetters_eq : Sporadic.ruPresentation.relatorLetters = ruSpec.rels := by
  rw [Sporadic.ruPresentation_relatorLetters]
  rfl

noncomputable def nativeEquiv :
    Blueprint.NativeSporadic.Ru ≃* J CFSG.Sporadic.Ru.Native.ruData :=
  seedEquiv CFSG.Sporadic.Ru.ruFacts.toBaseFacts

theorem card_J :
    Nat.card (J CFSG.Sporadic.Ru.Native.ruData) = 145926144000 := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.Ru.card_Ru]

end CFSG.Sporadic.Bridge.Ru
