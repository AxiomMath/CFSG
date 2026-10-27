module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC6Defs
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly


theorem twE6_normSmallR_data (h5 : GGTwE6EltNormSmallInput) (h3N : GGTwE6NormSmallThreeInput)
    (h3D : GGTwE6DeltaSmallThreeInput) {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) :
    GGOutdiagOdd p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ∧
      ∃ r, GGTorusLift p r (TwE6Delta.RecipeR K n) ∧
        GGStdSubTwoTorusNormSmallR p r (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ∧
          GGStdSubTwoTorusDeltaSmall p r (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  refine ⟨TwE6Delta.ggOutdiagOdd_twE6 hn hK p, TwE6Delta.liftRank p,
    ggTorusLift_twE6Add_holds hn hK hp hpn, ?_⟩
  by_cases hp3 : p = 3
  · subst hp3
    rw [TwE6Delta.liftRank_three]
    exact ⟨h3N K n hn hK hpn, h3D K n hn hK hpn⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : n ≠ 0))).1 hpn
    omega
  have hO := TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3
  have hC := TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3
  rw [TwE6Delta.liftRank_of_ne hp3]
  exact ⟨ggStdSubTwoTorusNormSmallR_of_small (ggStdSubTwoTorusNormSmall_of_elt hp hO
      (TwE6Delta.center_recipeR_eq_bot hn hK) hC (h5 K n p hn hK hp hpn hp3)),
    ggStdSubTwoTorusDeltaSmall_of_delta (ggStdSubTwoTorusDelta_of_prime hO hC)⟩

theorem ggStdSubSmallInputOn_twE6 (h5 : GGTwE6EltNormSmallInput)
    (h3N : GGTwE6NormSmallThreeInput) (h3D : GGTwE6DeltaSmallThreeInput) :
    GGStdSubSmallInputOn GGIOneMoreTwE6Label :=
  ggStdSubSmallInputOn_of_labels_normSmallR ggLNoncyclicInput_holds fun _ _ hp hlab h _ =>
    TwE6Delta.labelAll h.1 fun _ _ _ hK => twE6_normSmallR_data h5 h3N h3D hlab.1 hK hp h.2

end CFSG.StandardType.SmallExc

end
