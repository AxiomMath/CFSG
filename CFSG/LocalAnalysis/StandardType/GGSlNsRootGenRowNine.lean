module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenTwoAsm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourDom
public import CFSG.LocalAnalysis.StandardType.GGRootGenQTwoQFour

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem recipeLinear_rootGenAvoidKG_rowNine {d : ℕ} (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ 1) Q) :
    LargeEvenRecipeLinear d (2 ^ 1) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift 3 r R ∧ GGTorusRootGenAvoidKG 3 r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 0,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL hd)),
    ggTorusRootGenAvoidKG_linearNs_two (by simpa using hK) 0⟩

theorem ggRootGenKGAvoidOn_rowNine : GGRootGenKGAvoidOn GGRootGenRowNineLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨rfl, rfl, rfl, hl⟩
  dsimp only at hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeLinear_rootGenAvoidKG_rowNine (by omega) hQ

theorem ggRootGenNbrInputOnQFour_of_notRowNine {X : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (X p lab ∨ GGRootGenRowNineLabel p lab)) :
    GGRootGenNbrInputOnQFour fun p lab => GGRootGenOpenLabel p lab ∧ ¬ X p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab =>
      GGRootGenRowNineLabel p lab ∨ (GGRootGenOpenLabel p lab ∧
        ¬ (X p lab ∨ GGRootGenRowNineLabel p lab)))
      (fun lab hlab => (em (GGRootGenRowNineLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim hlab.2 hn⟩) hK).elim_or with h₁ | h₂
  · exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_rowNine hHyp hnb h₁
  · exact h G p B Bs x L D J hHyp hq hN y K hnb h₂

end CFSG.StandardType

end
