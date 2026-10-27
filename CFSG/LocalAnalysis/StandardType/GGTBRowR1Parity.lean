module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTBRowR1_largeEvenSplit_untwisted {p : ℕ} {lab : LargeEvenLabel}
    (ht : GGTBRowR1 p lab) (hn : 2 ≤ lab.n) : LargeEvenSplit p lab ↔ p ∣ 2 ^ lab.n - 1 := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGTBRowR1 GGTBRowR1A GGTBRowR1D GGTBRowR1E6 GGTBRowR1E7 GGTBRowR1E8 at ht
  simp only at ht hn
  have hn1 : n ≠ 1 := by omega
  rcases ht with ⟨ht, -⟩ | ht | ht | ht | ht <;> subst ht <;>
    simp [LargeEvenSplit, LargeEvenUntwisted, hn1]

theorem ggInnerDiagOnLabel_r1Par_of_closed (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {P : ℕ → LargeEvenLabel → Prop} (hPR : ∀ {lab}, P p lab → GGTBRowR1 p lab)
    (hPiso : ∀ {lab lab'}, P p lab → GGLabelIso lab lab' → lab'.n = lab.n ∧ P p lab')
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ P p lab) p Bs L) :
    GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ P p lab ∧ p ∣ 2 ^ lab.n - 1) p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  have hiso : GGLabelIso lab1 labs := hRig lab1 labs _ hlab1 hlabs hhas1 hhass
  obtain ⟨hn', hrow'⟩ := hPiso hrow hiso
  have hbad : GGLabQFour p labs ∧ P p labs ∧ p ∣ 2 ^ labs.n - 1 := by
    have hq' : 2 ≤ labs.n := by rw [hn']; exact hQ4
    exact ⟨by unfold GGLabQFour; exact hq', hrow',
      (ggTBRowR1_largeEvenSplit_untwisted (hPR hrow') hq').mp hPs.1⟩
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlabs hhass
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

end CFSG.StandardType

end
