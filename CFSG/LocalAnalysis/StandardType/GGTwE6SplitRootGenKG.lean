module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenSCFive
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenSCThree
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidCenterPrime
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem ggTorusRootGenAvoidKG_twE6Split
    {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusRootGenAvoidKG p 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have := TwE6Delta.finite_recipeR (K := K) hK
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  by_cases hp3 : p = 3
  · subst hp3
    have h3' : ¬ 3 ∣ 2 ^ n + 1 := fun h => by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    refine ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime hp hZ
      (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hn hK h3' hφ)
      (TwE6Delta.ggCenterPrime_three_twE6 hn hK h3') fun E hE h4 _ hsc => ?_
    exact TwE6SplitRootGen.ggTorusModelAt_recipeR_twE6Split_three hn hK hpn hE h4 hsc
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra h
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    refine ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime hp hZ
      (TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3) (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      fun E hE _ _ hsc => ?_
    exact TwE6SplitRootGen.ggTorusModelAt_recipeR_twE6Split_of_five_le hn hK hp hp5 hpn hE hsc

end CFSG.StandardType

end
