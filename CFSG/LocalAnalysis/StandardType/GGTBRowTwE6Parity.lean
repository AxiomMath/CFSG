module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadLabelParity
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTBRowR6_largeEvenSplit_twE6_iff {p : ℕ} {lab : LargeEvenLabel}
    (htag : lab.tag = .twE6) :
    LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n + 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  simp [LargeEvenSplit, LargeEvenUntwisted]

@[expose] def GGTBTwE6PlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ p ≠ 3

theorem ggInnerDiagOnLabel_twE6Plus_of_rowR6 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR6 p lab) p Bs L) :
    GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨-, hrow⟩ := hP1.1
  unfold GGTBRowR6 at hrow
  have heq : labs = lab1 :=
    eq_of_ggLabelIso_of_twE6 hrow.1 (hRig labs lab1 _ hlabs hlab1 hhass hhas1)
  have hs : LargeEvenSplit p lab1 := by
    have h := hPs.1
    rwa [heq] at h
  have hdvd : p ∣ 2 ^ lab1.n + 1 := by
    rcases (ggTBRowR6_largeEvenSplit_twE6_iff hrow.1).mp hs with hd | ⟨-, hp3⟩
    · exact hd
    · exact absurd hp3 hrow.2
  have hbad : GGTBTwE6PlusLabel p lab1 := ⟨hrow.1, hdvd, hrow.2⟩
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlab1 hhas1
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

theorem ggTBRowR6_p_ne_three
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G}
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR6 p lab) p Bs L) :
    p ≠ 3 := by
  obtain ⟨lab1, _, _, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨-, hrow⟩ := hP1.1
  unfold GGTBRowR6 at hrow
  exact hrow.2

end CFSG.StandardType

end
