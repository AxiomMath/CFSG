module

public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Presentation.J3
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.J3.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9119
public import Certificates.Certificate9211
public import Certificates.Certificate3169
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Bridge.J3

open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.J3 (a b J rep_a rep_b faithful j3Facts seedEquiv closure_ab)
open CFSG.Sporadic.J3.Native (j3Data)

private theorem presentation_eq : SporadicName.J3.presentation = Sporadic.j3Presentation := rfl

theorem generatorCount_eq : Sporadic.j3Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem relators_eval :
    ∀ v ∈ Sporadic.j3Presentation.relatorLetters,
    wordProd (img2 (a j3Data) (b j3Data)) v = 1 :=
  Certificates.certificate9211

private theorem seedA_eq : j3Data.seedA = Blueprint.NativeSporadic.J3Seed1 := rfl

private theorem seedB_eq : j3Data.seedB = Blueprint.NativeSporadic.J3Seed2 := rfl

noncomputable def nativeEquiv :
    Blueprint.NativeSporadic.J3 ≃* J j3Data := by
  have e := seedEquiv j3Facts.powA j3Facts.powB
  rw [seedA_eq, seedB_eq] at e
  exact e

theorem le_card_J : 50232960 ≤ Nat.card (J j3Data) := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.J3.card_J3]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.J3.Group)
    (hcard : Nat.card SporadicName.J3.Group ≤ 50232960) :
    Nonempty (Blueprint.NativeSporadic.J3 ≃* SporadicName.J3.Group) := by
  revert hfin hcard
  show Finite SporadicName.J3.presentation.Group →
    Nat.card SporadicName.J3.presentation.Group ≤ 50232960 →
    Nonempty (Blueprint.NativeSporadic.J3 ≃* SporadicName.J3.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_closure Sporadic.j3Presentation generatorCount_eq
    (closure_ab j3Data) relators_eval hcard le_card_J
  exact ⟨nativeEquiv.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.J3 ≃* SporadicName.J3.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.J3.finite_card_le.1
    Presentation.J3.finite_card_le.2

end CFSG.Sporadic.Bridge.J3
