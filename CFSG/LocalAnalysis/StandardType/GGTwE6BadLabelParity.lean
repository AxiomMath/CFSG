module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggInnerDiagOnLabel_twE6Bad_and_of_three (hRig : GGLabelRigidInput)
    {Q : ℕ → LargeEvenLabel → Prop}
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => Q p lab ∧ lab.tag = .twE6 ∧ p = 3) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => Q p lab ∧ GGTwE6BadLabel p lab) p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ, htag, hp3⟩ := hP1.1
  have heq : labs = lab1 :=
    eq_of_ggLabelIso_of_twE6 htag (hRig labs lab1 _ hlabs hlab1 hhass hhas1)
  subst hp3
  have hs : LargeEvenSplit 3 labs := hPs.1
  rw [heq] at hs
  have hbad : GGTwE6BadLabel 3 lab1 := by
    refine ⟨htag, rfl, ?_⟩
    unfold LargeEvenSplit at hs
    rcases hs with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨hn, -⟩
    · rw [htag] at hu
      exact hu.elim
    · exact h
    · rcases h with h | h <;> rw [htag] at h <;> cases h
    · rw [hn]
      norm_num
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlab1 hhas1
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact ⟨hQ, hbad⟩, hBN, hBI⟩

theorem ggInnerDiagOnLabel_twE6Bad_of_three (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p = 3) p Bs L) :
    GGInnerDiagOnLabel GGTwE6BadLabel p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩)
    (ggInnerDiagOnLabel_twE6Bad_and_of_three (Q := fun _ _ => True) hRig hHyp
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨trivial, hP.1⟩, hP.2⟩) hL))

end CFSG.StandardType

end
