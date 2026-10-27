module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPAll

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16fh_three_rk_of_eq_bot {X : Type} [CommGroup X] {L : Subgroup (MulAut X)}
    (h : commSub ⊤ L ⊓ fixV L = ⊥) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  rw [h, rk_bot, Nat.mul_zero]
  exact Nat.zero_le _

theorem k_fixHalfRows_holds :
    K_FixHalfRows := by
  refine ⟨?_, ?_⟩
  · intro X _ _ hX L hrow
    have hJP := k_JonesParshallH1_holds X hX L
    rcases hrow with hL3 | hA5 | hS2 | hS3 | hO2 | hO3 | ⟨hSt, hirr⟩
    · exact s16fh_row_L3 hX hL3
    · exact s16fh_three_rk_of_eq_bot (hJP.1 (Or.inl hA5))
    · exact s16fh_row_SL2_two hS2 (hJP.2 hS2)
    · exact s16fh_row_SL2_three hX hS3
    · exact s16fh_three_rk_of_eq_bot (hJP.1 (Or.inr (Or.inl hO2)))
    · exact s16fh_three_rk_of_eq_bot (hJP.1 (Or.inr (Or.inr (Or.inl hO3))))
    · exact s16fh_three_rk_of_eq_bot (hJP.1 (Or.inr (Or.inr (Or.inr ⟨hSt, hirr⟩))))
  · intro X _ _ hX L U Z n hn6 hn8 hAlt hUinv hUc hZ hsum
    exact s16fh_row_alt hX hn6 hn8 hAlt hUinv hUc hZ hsum

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
