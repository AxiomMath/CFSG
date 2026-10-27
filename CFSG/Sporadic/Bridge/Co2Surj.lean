module

public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Co2.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9203
public import Certificates.Certificate3138
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Bridge.Co2

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.Co2.Native (co2Data)

private theorem presentation_eq : SporadicName.Co2.presentation = Sporadic.co2Presentation := rfl

theorem generatorCount_eq : Sporadic.co2Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

noncomputable abbrev JD : Subgroup (GL (Fin co2Data.d) (ZMod 2)) :=
  J co2Data

theorem baseFacts : BaseFacts co2Data :=
  CFSG.Sporadic.Co2.co2Facts.toBaseFacts

theorem relators_eval :
    ∀ v ∈ Sporadic.co2Presentation.relatorLetters,
    wordProd (img2 (a co2Data) (b co2Data)) v = 1 :=
  Certificates.certificate9203

noncomputable def nativeEquiv : Blueprint.NativeSporadic.Co2 ≃* JD :=
  seedEquiv baseFacts

theorem le_card_J : 42305421312000 ≤ Nat.card JD := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.Co2.card_Co2]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Co2.Group)
    (hcard : Nat.card SporadicName.Co2.Group ≤ 42305421312000) :
    Nonempty (Blueprint.NativeSporadic.Co2 ≃* SporadicName.Co2.Group) := by
  revert hfin hcard
  show Finite SporadicName.Co2.presentation.Group →
    Nat.card SporadicName.Co2.presentation.Group ≤ 42305421312000 →
    Nonempty (Blueprint.NativeSporadic.Co2 ≃* SporadicName.Co2.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_closure Sporadic.co2Presentation generatorCount_eq
    (closure_ab co2Data) relators_eval hcard le_card_J
  exact ⟨nativeEquiv.trans e⟩

end CFSG.Sporadic.Bridge.Co2
