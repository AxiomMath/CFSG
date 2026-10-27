module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTBRowR5_labelIso_twisted {lab lab' : LargeEvenLabel}
    (ht : lab.tag = .twA ∨ lab.tag = .twD) (hr : 3 ≤ lab.rank) (h : GGLabelIso lab lab') :
    (lab'.tag = .twA ∨ lab'.tag = .twD) ∧ lab'.n = lab.n ∧ lab'.rank = lab.rank := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  simp only at ht hr
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · injection h with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨ht, rfl, rfl⟩
  · rcases ht with ht | ht <;> rcases h.1 with hb | hb <;> simp_all
  · injection h.1 with h1 h2 h3
    subst h1
    rcases ht with ht | ht <;> exact absurd ht (by decide)
  · injection h.1 with h1 h2 h3
    subst h1
    rcases ht with ht | ht <;> exact absurd ht (by decide)
  · obtain ⟨h1, h2⟩ := h
    injection h1 with ht1 hr1 hn1
    injection h2 with ht2 hr2 hn2
    subst ht2; subst hr2; subst hr1
    exact ⟨Or.inl rfl, hn2, rfl⟩
  · obtain ⟨h1, h2⟩ := h
    injection h1 with ht1 hr1 hn1
    injection h2 with ht2 hr2 hn2
    subst ht2; subst hr2; subst hr1
    exact ⟨Or.inr rfl, hn2, rfl⟩
  · obtain ⟨h1, h2⟩ := h
    injection h1 with ht1 hr1 hn1
    subst hr1
    exfalso
    omega
  · obtain ⟨h1, h2⟩ := h
    injection h2 with ht2 hr2 hn2
    subst ht2
    rcases ht with ht | ht <;> simp_all

private theorem ggTBRowR5_largeEvenSplit_twisted {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .twA ∨ lab.tag = .twD) (hn : 2 ≤ lab.n) :
    LargeEvenSplit p lab ↔
      (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n + 1 ∨ p ∣ 2 ^ lab.n - 1)) := by
  obtain ⟨t, r, n⟩ := lab
  rcases ht with ht | ht <;> dsimp only at ht hn <;> subst ht
  · have hn1 : n ≠ 1 := by omega
    constructor
    · intro h
      simpa [LargeEvenSplit, LargeEvenUntwisted, hn1] using h
    · intro h
      simpa [LargeEvenSplit, LargeEvenUntwisted, hn1] using h
  · have hn1 : n ≠ 1 := by omega
    constructor
    · intro h
      simpa [LargeEvenSplit, LargeEvenUntwisted, hn1] using h
    · intro h
      simpa [LargeEvenSplit, LargeEvenUntwisted, hn1] using h

theorem ggInnerDiagOnLabel_r5Par_of_rowR5 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5 p lab) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5Par p lab) p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  unfold GGTBRowR5 at hrow
  have hiso : GGLabelIso lab1 labs := hRig lab1 labs _ hlab1 hlabs hhas1 hhass
  obtain ⟨htag', hn', hrank'⟩ := ggTBRowR5_labelIso_twisted hrow.1 hrow.2 hiso
  have hbad : GGLabQFour p labs ∧ GGTBRowR5Par p labs := by
    refine ⟨?_, ⟨⟨htag', ?_⟩, ?_⟩⟩
    · unfold GGLabQFour
      rw [hn']
      exact hQ4
    · rw [hrank']
      exact hrow.2
    · exact (ggTBRowR5_largeEvenSplit_twisted htag' (by rw [hn']; exact hQ4)).mp hPs.1
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlabs hhass
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

end CFSG.StandardType

end
