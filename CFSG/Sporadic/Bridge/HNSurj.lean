module

public import CFSG.Sporadic.HN
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Presentation.HN
public import Certificates.Data.CFSGNative.Bridge.HNGPL
public meta import Certificates.Data.CFSGNative.Bridge.HNGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9114
public import Certificates.Certificate9208
public import Certificates.Certificate3166
public import CFSG.Sporadic.Bridge.HomSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Bridge.HN

open CFSG.Sporadic.F5 CFSG.Sporadic.Bridge.SurjD.Native TauCeti

theorem bridge_hom :
    ∃ φ : Sporadic.hnPresentation.Group →*
      GL (Fin (CFSG.Sporadic.HN.Native.hnData ()).d) (ZMod 5),
    J CFSG.Sporadic.HN.Native.hnData ≤ φ.range :=
  Certificates.certificate9208

private theorem presentation_eq : SporadicName.HN.presentation = Sporadic.hnPresentation := rfl

theorem generatorCount_eq : Sporadic.hnPresentation.generatorCount = hnSpec.m := by
  simp [GroupPresentation.generatorCount, hnSpec]

theorem relatorLetters_eq : Sporadic.hnPresentation.relatorLetters = hnSpec.rels := by
  simp only [hnSpec, hnRels, GroupPresentation.relatorLetters_def,
    GroupPresentation.relators_def, Sporadic.hnPresentation_transcribed, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  rfl

noncomputable def nativeEquiv :
    Blueprint.NativeSporadic.HN ≃* J CFSG.Sporadic.HN.Native.hnData :=
  CFSG.Sporadic.HN.hnSeedEquiv

theorem card_J :
    Nat.card (J CFSG.Sporadic.HN.Native.hnData) = 273030912000000 := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.HN.card_HN]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.HN.Group)
    (hcard : Nat.card SporadicName.HN.Group ≤ 273030912000000) :
    Nonempty (Blueprint.NativeSporadic.HN ≃* SporadicName.HN.Group) := by
  revert hfin hcard
  show Finite SporadicName.HN.presentation.Group →
    Nat.card SporadicName.HN.presentation.Group ≤ 273030912000000 →
    Nonempty (Blueprint.NativeSporadic.HN ≃* SporadicName.HN.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨φ, hφ⟩ := bridge_hom
  obtain ⟨e⟩ := nonempty_mulEquiv_of_le_range φ hφ hcard (le_of_eq card_J.symm)
  exact ⟨nativeEquiv.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.HN ≃* SporadicName.HN.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.HN.finite_card_le.1 Presentation.HN.finite_card_le.2

end CFSG.Sporadic.Bridge.HN
