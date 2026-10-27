module

public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Presentation.Co3
public import Certificates.Data.CFSGNative.Bridge.SurjD
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9105
public import Certificates.Certificate9204
public import Certificates.Certificate3091
public import CFSG.Sporadic.Bridge.HomSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.Co3

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native TauCeti

theorem bridge_hom :
    ∃ φ : Sporadic.co3Presentation.Group →*
      GL (Fin (CFSG.Sporadic.Co3.Native.co3Data ()).d) (ZMod 2),
    J CFSG.Sporadic.Co3.Native.co3Data ≤ φ.range :=
  Certificates.certificate9204

private theorem presentation_eq : SporadicName.Co3.presentation = Sporadic.co3Presentation := rfl

theorem generatorCount_eq : Sporadic.co3Presentation.generatorCount = co3Spec.m := by
  simp [GroupPresentation.generatorCount, co3Spec]

theorem relatorLetters_eq : Sporadic.co3Presentation.relatorLetters = co3Spec.rels := by
  simp only [co3Spec, co3Rels, GroupPresentation.relatorLetters_def,
    GroupPresentation.relators_def, Sporadic.co3Presentation_transcribed, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_mul, Relator.toWord_pow]
  rfl

noncomputable def nativeEquiv :
    Blueprint.NativeSporadic.Co3 ≃* J CFSG.Sporadic.Co3.Native.co3Data :=
  seedEquiv CFSG.Sporadic.Co3.co3Facts.toBaseFacts

theorem card_J :
    Nat.card (J CFSG.Sporadic.Co3.Native.co3Data) = 495766656000 := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.Co3.card_Co3]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Co3.Group)
    (hcard : Nat.card SporadicName.Co3.Group ≤ 495766656000) :
    Nonempty (Blueprint.NativeSporadic.Co3 ≃* SporadicName.Co3.Group) := by
  revert hfin hcard
  show Finite SporadicName.Co3.presentation.Group →
    Nat.card SporadicName.Co3.presentation.Group ≤ 495766656000 →
    Nonempty (Blueprint.NativeSporadic.Co3 ≃* SporadicName.Co3.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨φ, hφ⟩ := bridge_hom
  obtain ⟨e⟩ := nonempty_mulEquiv_of_le_range φ hφ hcard (le_of_eq card_J.symm)
  exact ⟨nativeEquiv.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Co3 ≃* SporadicName.Co3.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Co3.finite_card_le.1
    Presentation.Co3.finite_card_le.2

end CFSG.Sporadic.Bridge.Co3
