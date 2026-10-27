module

public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Presentation.Co1
public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.CFSGNative.Bridge.SurjD
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9100
public import Certificates.Certificate9202
public import Certificates.Certificate3024
public import CFSG.Sporadic.Bridge.HomSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.Co1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native TauCeti

theorem bridge_hom :
    ∃ φ : Sporadic.co1Presentation.Group →*
      GL (Fin (CFSG.Sporadic.Co1.Native.co1Data ()).d) (ZMod 2),
    J CFSG.Sporadic.Co1.Native.co1Data ≤ φ.range :=
  Certificates.certificate9202

private theorem presentation_eq : SporadicName.Co1.presentation = Sporadic.co1Presentation := rfl

theorem generatorCount_eq : Sporadic.co1Presentation.generatorCount = co1Spec.m := by
  simp [GroupPresentation.generatorCount, co1Spec]

theorem relatorLetters_eq : Sporadic.co1Presentation.relatorLetters = co1Spec.rels := by
  rw [Sporadic.co1Presentation_relatorLetters]
  rfl

noncomputable def nativeEquiv :
    Blueprint.NativeSporadic.Co1 ≃* J CFSG.Sporadic.Co1.Native.co1Data :=
  seedEquiv CFSG.Sporadic.Co1.co1Facts.toBaseFacts

theorem card_J :
    Nat.card (J CFSG.Sporadic.Co1.Native.co1Data) = 4157776806543360000 := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.Co1.card_Co1]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Co1.Group)
    (hcard : Nat.card SporadicName.Co1.Group ≤ 4157776806543360000) :
    Nonempty (Blueprint.NativeSporadic.Co1 ≃* SporadicName.Co1.Group) := by
  revert hfin hcard
  show Finite SporadicName.Co1.presentation.Group →
    Nat.card SporadicName.Co1.presentation.Group ≤ 4157776806543360000 →
    Nonempty (Blueprint.NativeSporadic.Co1 ≃* SporadicName.Co1.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨φ, hφ⟩ := bridge_hom
  obtain ⟨e⟩ := nonempty_mulEquiv_of_le_range φ hφ hcard (le_of_eq card_J.symm)
  exact ⟨nativeEquiv.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Co1 ≃* SporadicName.Co1.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Co1.finite_card_le.1
    Presentation.Co1.finite_card_le.2

end CFSG.Sporadic.Bridge.Co1
