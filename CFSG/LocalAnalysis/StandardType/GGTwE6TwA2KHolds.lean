module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDescent
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KThreeDvd
import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KRank

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly

theorem modelAt_holds
    (K : Type) [Field K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    ModelAt K σ n := by
  intro h hh3 hh1 J hJ hlab
  exact ⟨three_dvd_of_component K σ hn hK hσ h hh3 hh1 J hJ hlab,
    fun A hA hhA => card_le_of_component K σ hn hK hσ h hh3 hh1 J hJ hlab A hA hhA⟩

theorem ggTwE6TwA2CompKnown_holds :
    GGTwE6TwA2CompKnown := by
  refine ggTwE6TwA2CompKnown_of_modelR fun n K _ _ hK => ?_
  have hn : 1 ≤ n := by
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp at hK
      omega
    · omega
  exact modelR_of_modelAt hn hK fun σ hσ => modelAt_holds K σ hn hK hσ

end CFSG.StandardType.TwE6TwA2K

end
