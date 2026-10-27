module

public import CFSG.Sporadic.He
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Sporadic.Presentation.HeExact
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9118
public import Certificates.Certificate9210
public import Certificates.Certificate3168
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.He

open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.He (a b J rep_alpha rep_beta a_inv actionFacts)

private theorem presentation_eq : SporadicName.He.presentation = Sporadic.hePresentation := rfl

theorem generatorCount_eq : Sporadic.hePresentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem rep_alpha_inv : Rep 8330 CFSG.Sporadic.He.orb.alpha a⁻¹ := by
  rw [a_inv]
  exact rep_alpha

theorem relators_eval :
    ∀ v ∈ Sporadic.hePresentation.relatorLetters, wordProd (img2 a b) v = 1 :=
  Certificates.certificate9210

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.He.Group)
    (hcard : Nat.card SporadicName.He.Group ≤ 4030387200) :
    Nonempty (Blueprint.NativeSporadic.He ≃* SporadicName.He.Group) := by
  revert hfin hcard
  show Finite SporadicName.He.presentation.Group →
    Nat.card SporadicName.He.presentation.Group ≤ 4030387200 →
    Nonempty (Blueprint.NativeSporadic.He ≃* SporadicName.He.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_closure Sporadic.hePresentation generatorCount_eq
    CFSG.Sporadic.He.closure_ab relators_eval hcard (le_of_eq CFSG.Sporadic.He.card_J.symm)
  exact ⟨CFSG.Sporadic.He.heEquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.He ≃* SporadicName.He.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.He.finite_card_le.1 Presentation.He.finite_card_le.2

end CFSG.Sporadic.Bridge.He
