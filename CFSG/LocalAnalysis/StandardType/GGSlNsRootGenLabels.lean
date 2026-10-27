module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem recipeLinear_rootGenAvoidKG_linPhiTwo {d n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ n) Q) :
    LargeEvenRecipeLinear d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 0,
    TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv d K)
      (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL hd)),
    ggTorusRootGenAvoidKG_linearNs hK hn hp hpq 0⟩

theorem ggRootGenKGAvoidOn_linPhiTwo : GGRootGenKGAvoidOn GGRootGenLinPhiTwoLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨hpn, hn, h⟩
  dsimp only at hpn hn h
  intro Q hQ
  rcases h with rfl | ⟨rfl, rfl⟩
  · have hl1 : 1 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeLinear_rootGenAvoidKG_linPhiTwo hp hpn hn (by omega) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    exact recipeLinear_rootGenAvoidKG_linPhiTwo hp hpn hn (by norm_num) hQ

end CFSG.StandardType

end
