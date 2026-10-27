module

public import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRootGenLInputOnQFour_of_notUnitaryCoprime
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n))) :
    GGRootGenLInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n) ∨ (GGRootGenOpenLabel p lab ∧
        ¬ (X p lab ∨ (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n))))
      (fun lab hlab => (em (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hL).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidOn_unitaryCoprime hHyp h₁
  · exact h G p B Bs x L D J hHyp hq hN h₂

theorem ggRootGenNbrInputOnQFour_of_notUnitaryCoprime
    {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n))) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n) ∨ (GGRootGenOpenLabel p lab ∧
        ¬ (X p lab ∨ (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n))))
      (fun lab hlab => (em (GGUnitaryCoprimeLabel p lab ∧ 2 ≤ lab.n)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hK).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_unitaryCoprime hHyp hnb h₁
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end CFSG.StandardType

end
