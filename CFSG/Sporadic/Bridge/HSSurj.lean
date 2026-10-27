module

public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Presentation.HSExact
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.HS.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9116
public import Certificates.Certificate9209
public import Certificates.Certificate3167
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Bridge.HS

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.HS.Native (hsData)

private theorem presentation_eq : SporadicName.HS.presentation = Sporadic.hsPresentation := rfl

theorem generatorCount_eq : Sporadic.hsPresentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

noncomputable abbrev JD : Subgroup (GL (Fin hsData.d) (ZMod 2)) :=
  J hsData

theorem baseFacts : BaseFacts hsData :=
  CFSG.Sporadic.HS.hsFacts.toBaseFacts

theorem relators_eval :
    ∀ v ∈ Sporadic.hsPresentation.relatorLetters,
    wordProd (img2 (a hsData) (b hsData)) v = 1 :=
  Certificates.certificate9209

noncomputable def nativeEquiv : Blueprint.NativeSporadic.HS ≃* JD :=
  seedEquiv baseFacts

theorem le_card_J : 44352000 ≤ Nat.card JD := by
  rw [← Nat.card_congr nativeEquiv.toEquiv, CFSG.Sporadic.HS.card_HS]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.HS.Group)
    (hcard : Nat.card SporadicName.HS.Group ≤ 44352000) :
    Nonempty (Blueprint.NativeSporadic.HS ≃* SporadicName.HS.Group) := by
  revert hfin hcard
  show Finite SporadicName.HS.presentation.Group →
    Nat.card SporadicName.HS.presentation.Group ≤ 44352000 →
    Nonempty (Blueprint.NativeSporadic.HS ≃* SporadicName.HS.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_closure Sporadic.hsPresentation generatorCount_eq
    (closure_ab hsData) relators_eval hcard le_card_J
  exact ⟨nativeEquiv.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.HS ≃* SporadicName.HS.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.HS.finite_card_le.1
    Presentation.HS.finite_card_le.2

end CFSG.Sporadic.Bridge.HS
