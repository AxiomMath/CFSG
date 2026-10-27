module

public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9216
public import Certificates.Certificate3170
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.McL

open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.McL (a b J orb rep_alpha rep_alpha_inv rep_beta actionChecks_parts)

private theorem presentation_eq : SporadicName.McL.presentation = Sporadic.mclPresentation := rfl

theorem generatorCount_eq : Sporadic.mclPresentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem relators_eval :
    ∀ v ∈ Sporadic.mclPresentation.relatorLetters, wordProd (img2 a b) v = 1 :=
  Certificates.certificate9216

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.McL.Group)
    (hcard : Nat.card SporadicName.McL.Group ≤ 898128000) :
    Nonempty (Blueprint.NativeSporadic.McL ≃* SporadicName.McL.Group) := by
  revert hfin hcard
  show Finite SporadicName.McL.presentation.Group →
    Nat.card SporadicName.McL.presentation.Group ≤ 898128000 →
    Nonempty (Blueprint.NativeSporadic.McL ≃* SporadicName.McL.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_closure Sporadic.mclPresentation generatorCount_eq
    CFSG.Sporadic.McL.closure_ab relators_eval hcard (le_of_eq CFSG.Sporadic.McL.card_J.symm)
  exact ⟨CFSG.Sporadic.McL.mclEquivJ.trans e⟩

end CFSG.Sporadic.Bridge.McL
