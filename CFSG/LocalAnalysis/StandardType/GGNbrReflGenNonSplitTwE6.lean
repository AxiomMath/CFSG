module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Plus
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGTwE6SplitWeylInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    5 ≤ p → p ∣ 2 ^ n - 1 → GGTorusReflGenW p 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

theorem ggNbrTableBWeylNonSplitOn_twE6_of
    (h : GGTwE6SplitWeylInput) : GGNbrTableBWeylNonSplitOn GGNbrNonSplitTwE6Label := by
  intro p hp hp2 lab hlab hS _
  obtain ⟨ht, hplus | hminus⟩ := hS
  · exact largeEvenLabelAll_reflGenW_twE6Plus hp hp2 hplus.1 hlab ⟨ht, hplus.2⟩
  · by_cases hp3 : p = 3
    · subst hp3
      exact largeEvenLabelAll_reflGenW_twE6Three hlab ⟨ht, hminus⟩
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by norm_num)
        omega
      exact TwE6Delta.labelAll ht fun K _ _ hK _ _ =>
        ⟨4, ggTorusLift_twE6Dvd_holds hlab.1 hK hp hp2 hminus,
          h K lab.n p hlab.1 hK hp hp5 hminus⟩

end CFSG.StandardType

end
