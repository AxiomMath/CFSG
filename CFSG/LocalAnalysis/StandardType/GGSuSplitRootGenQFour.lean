module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRootGenLInputOnQFour_of_notUnitarySplit
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenUnitarySplitLabel p lab)) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      GGRootGenUnitarySplitLabel p lab ∨ (GGRootGenOpenLabel p lab ∧
        ¬ (X p lab ∨ GGRootGenUnitarySplitLabel p lab)))
      (fun lab hlab => (em (GGRootGenUnitarySplitLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hL).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidOn_unitarySplit hHyp h₁
  · exact h G p B Bs x L D J hHyp hq hN h₂

theorem ggRootGenNbrInputOnQFour_of_notUnitarySplit
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenUnitarySplitLabel p lab)) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      GGRootGenUnitarySplitLabel p lab ∨ (GGRootGenOpenLabel p lab ∧
        ¬ (X p lab ∨ GGRootGenUnitarySplitLabel p lab)))
      (fun lab hlab => (em (GGRootGenUnitarySplitLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hK).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_unitarySplit hHyp hnb h₁
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end CFSG.StandardType

end
