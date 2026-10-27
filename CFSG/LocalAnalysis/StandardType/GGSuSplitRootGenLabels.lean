module

public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRootGenUnitarySplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧ (lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3))

private theorem recipeUnitary_rootGenAvoidKG
    {d n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) (hn : 1 ≤ n) (hd : 3 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := (TableBU.unitaryFieldData_of_card hK hn).charP
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 0,
    TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := d) (f := n) (K := K)
      (by omega)),
    ggTorusRootGenAvoidKG_unitarySplit hK hd hp hpq 0⟩

theorem ggRootGenKGAvoidOn_unitarySplit :
    GGRootGenKGAvoidOn GGRootGenUnitarySplitLabel := by
  rintro p ⟨t, l, n⟩ hp _ hlab ⟨hpn, htag⟩
  dsimp only at hpn htag
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with h | ⟨h, hl⟩
  · subst h
    dsimp only [LargeEvenInLambda2] at hlab
    have hl2 : 2 ≤ l := hlab.2.1
    exact recipeUnitary_rootGenAvoidKG (d := l + 1) hp hpn hn (by omega) hQ
  · subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide),
      ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    exact recipeUnitary_rootGenAvoidKG hp hpn hn (by norm_num) hQ

end CFSG.StandardType

end
