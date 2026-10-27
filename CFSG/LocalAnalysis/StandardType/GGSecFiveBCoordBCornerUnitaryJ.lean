module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux3
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusLocalize
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open GGQ2Frame
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem corner_hasLabel_twA_J_of_extension_full {G : Type} [Group G]
    {L J : Subgroup G} {H E : Subgroup ↥L} {r : ℕ}
    (R : Realization H E (planeEntry .symplectic r))
    {u : PlaneRaw.V r}
    (hc : (planeEntry .symplectic r).admissible (.extension u))
    (hu : ∀ i, u i ≠ 0)
    (hJ : J = (R.component (.extension u)).map L.subtype) :
    GGHasLabel ⟨.twA, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  classical
  let A : Subgroup ↥L := R.component (.extension u)
  have hs : PlaneRaw.Code.extSupport u = Finset.univ := by
    ext i
    simp [PlaneRaw.Code.extSupport, hu i]
  have hlabel : (planeEntry .symplectic r).label (.extension u) = ⟨.twA, r - 1, 1⟩ := by
    change PlaneRaw.label .symplectic (.extension u) = ⟨.twA, r - 1, 1⟩
    simp only [PlaneRaw.label, hs, Finset.card_univ, Fintype.card_fin]
  obtain ⟨lab, hbody⟩ := largeEvenMarking_exists_hasLabel (R.marked (.extension u) hc)
  have hlab : GGHasLabel lab (↥A ⧸ Subgroup.center ↥A) := hbody.2.1
  obtain ⟨_, _, _, _, _, hP⟩ := hbody.2.2
  rw [hP, hlabel] at hlab
  have hquot : (↥A ⧸ Subgroup.center ↥A) ≃*
      (↥(A.map L.subtype) ⧸ Subgroup.center ↥(A.map L.subtype)) :=
    QuotientGroup.congr _ _ (Subgroup.equivMapOfInjective A L.subtype L.subtype_injective)
      (Subgroup.map_center_eq _)
  have h : GGHasLabel ⟨.twA, r - 1, 1⟩
      (↥(A.map L.subtype) ⧸ Subgroup.center ↥(A.map L.subtype)) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨hquot.symm.trans f⟩) hlab
  subst hJ
  exact h

end CFSG.StandardType

end
