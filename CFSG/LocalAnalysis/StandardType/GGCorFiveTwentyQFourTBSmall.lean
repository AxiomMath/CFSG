module

public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGInnerDiagOnLabel.mono_label_of_hasLabel {G : Type} [Group G]
    {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}
    (hST : ∀ lab, LargeEvenInLambda2 lab → GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) →
      S p lab → T p lab)
    (h : GGInnerDiagOnLabel S p Bs L) : GGInnerDiagOnLabel T p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have has : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  exact ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun R _ I F hP => by
      obtain ⟨hs, hna, θ, hcont⟩ := hP
      exact ⟨hs, hna, θ, ⟨hST lab hlab has hcont.1, hcont.2⟩⟩) hraw⟩

theorem ggExcReflTBInputQFourOn_of_cover {S S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → S₁ p lab ∨ S₂ p lab) (h₁ : GGExcReflTBInputQFourOn S₁)
    (h₂ : GGExcReflTBInputQFourOn S₂) : GGExcReflTBInputQFourOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => S₁ p lab ∨ S₂ p lab) (hS p)
    hL).elim_or with h | h
  · exact h₁ G p B Bs x L D J hHyp hq hN h
  · exact h₂ G p B Bs x L D J hHyp hq hN h

theorem ggExcReflTBInputQFourOn_smallRank :
    GGExcReflTBInputQFourOn fun p lab => GGLabQFour p lab ∧ GGRootGenSmallRankLabel p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hL' : GGInnerDiagOnLabel GGRootGenSmallRankLabel p Bs L :=
    GGInnerDiagOnLabel.mono_label (fun _ h => h.2) hL
  exact absurd (ggInnerDiagOnLabel_L_pRank_ge_three hHyp.1 hL')
    (not_largeEvenMarking_smallRank (X := ↥L) hp hp2)

theorem ggExcReflTBInputQFourOn_smallExc
    (hRig : GGLabelRigidInput) :
    GGExcReflTBInputQFourOn fun p lab => GGLabQFour p lab ∧ GGRootGenSmallExcLabel p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨lab₀, hlab₀, has₀, R₀, _, I₀, F₀, θ₀, hP₀⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hL' : GGInnerDiagOnLabel
      (fun p lab => GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) p Bs L := by
    refine GGInnerDiagOnLabel.mono_label_of_hasLabel
      (S := fun p lab => GGLabQFour p lab ∧ GGRootGenSmallExcLabel p lab) ?_ hL
    intro lab hlab has hS
    have hexc : GGRootGenSmallExcLabel p lab := hS.2
    have hiso : GGLabelIso lab lab₀ :=
      hRig lab lab₀ (↥L ⧸ Subgroup.center ↥L) hlab hlab₀ has has₀
    have hne : lab.tag ≠ .B ∧ lab.tag ≠ .C ∧ lab.tag ≠ .D ∧ lab.tag ≠ .A ∧ lab.tag ≠ .twD ∧
        lab.tag ≠ .twA := by
      rcases hexc with h | h | h <;> rw [h] <;> decide
    obtain ⟨hB, hC, hD, hA, hTD, hTA⟩ := hne
    have heq : lab = lab₀ := by
      rcases hiso with h | ⟨hBC, -⟩ | ⟨hDD, -⟩ | ⟨hAA, -⟩ | ⟨hTD', -⟩ | ⟨hTA', -⟩ | ⟨hTD'', -⟩ |
        ⟨-, hAA'⟩
      · exact h
      · exact absurd hBC (by rintro (h | h); exacts [hB h, hC h])
      · exact absurd (congrArg LargeEvenLabel.tag hDD) hD
      · exact absurd (congrArg LargeEvenLabel.tag hAA) hA
      · exact absurd (congrArg LargeEvenLabel.tag hTD') hTD
      · exact absurd (congrArg LargeEvenLabel.tag hTA') hTA
      · exact absurd (congrArg LargeEvenLabel.tag hTD'') hTD
      · exact absurd (congrArg LargeEvenLabel.tag hAA') hA
    refine ⟨hexc, ?_⟩
    unfold GGRootGenOpenLabel
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact ggLabPhiOneTwo_of_largeEvenSplit hP₀.1
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact hA h
      · exact hD h
      · exact hTD h
  exact absurd (ggInnerDiagOnLabel_L_pRank_ge_three hHyp.1 hL')
    (not_largeEvenMarking_smallExc (X := ↥L) hp hp2)

theorem ggExcReflTBInputQFourOn_of_notSmall
    (hRig : GGLabelRigidInput)
    (h : GGExcReflTBInputQFourOn fun p lab => GGLabQFour p lab ∧
      ¬ (GGRootGenSmallRankLabel p lab ∨ GGRootGenSmallExcLabel p lab)) :
    GGExcReflTBInputQFourOn GGLabQFour :=
  ggExcReflTBInputQFourOn_of_cover (S₁ := fun p lab => GGLabQFour p lab ∧
      (GGRootGenSmallRankLabel p lab ∨ GGRootGenSmallExcLabel p lab))
    (S₂ := fun p lab => GGLabQFour p lab ∧
      ¬ (GGRootGenSmallRankLabel p lab ∨ GGRootGenSmallExcLabel p lab))
    (fun p lab hq => (em (GGRootGenSmallRankLabel p lab ∨ GGRootGenSmallExcLabel p lab)).imp
      (fun hs => ⟨hq, hs⟩) (fun hn => ⟨hq, hn⟩))
    (ggExcReflTBInputQFourOn_of_cover
      (fun _ _ h => h.2.elim (fun hs => Or.inl ⟨h.1, hs⟩) fun hs => Or.inr ⟨h.1, hs⟩)
      ggExcReflTBInputQFourOn_smallRank (ggExcReflTBInputQFourOn_smallExc hRig)) h

end CFSG.StandardType

end
