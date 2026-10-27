module

public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Sporadic.Presentation.Fi22Exact
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9205
public import Certificates.Certificate1005
public import Certificates.Certificate9107
public import Certificates.Certificate9108
public import Certificates.Certificate9109
public import Certificates.Certificate9110
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTableOrders
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Fi22ExactCover
public import CFSG.Sporadic.Presentation.Fi22ExactTop
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Bridge.Fi22

open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.Fi22 (a b J orb rep_alpha rep_beta a_inv actionChecks_parts)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem presentation_eq : SporadicName.Fi22.presentation = Sporadic.fi22Presentation :=
  rfl

theorem generatorCount_eq : Sporadic.fi22Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem rep_alpha_inv : Rep 3510 orb.alpha a⁻¹ := by
  rw [a_inv]
  exact rep_alpha

theorem relators_eval :
    ∀ v ∈ Sporadic.fi22Presentation.relatorLetters, wordProd (img2 a b) v = 1 :=
  Certificates.certificate9205

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Fi22.Group)
    (hcard : Nat.card SporadicName.Fi22.Group ≤ 64561751654400) :
    Nonempty (Blueprint.NativeSporadic.Fi22 ≃* SporadicName.Fi22.Group) := by
  revert hfin hcard
  show Finite SporadicName.Fi22.presentation.Group →
    Nat.card SporadicName.Fi22.presentation.Group ≤ 64561751654400 →
    Nonempty (Blueprint.NativeSporadic.Fi22 ≃* SporadicName.Fi22.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_closure Sporadic.fi22Presentation generatorCount_eq
    CFSG.Sporadic.Fi22.closure_ab relators_eval hcard
    (le_of_eq CFSG.Sporadic.Fi22.card_J.symm)
  exact ⟨CFSG.Sporadic.Fi22.fi22EquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Fi22 ≃* SporadicName.Fi22.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Fi22.finite_card_le.1
    Presentation.Fi22.finite_card_le.2

end CFSG.Sporadic.Bridge.Fi22
