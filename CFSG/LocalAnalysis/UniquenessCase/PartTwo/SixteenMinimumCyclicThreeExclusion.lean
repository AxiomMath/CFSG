module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMinimumChoice

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem false_of_card_three_rk_six_min
    {G : Type} [Group G] [Finite G]
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : MinChoiceSupport.Conc4_136Min D V₀ V hV L)
    (hm : mBar D.M V₀ V hV ≤ 2)
    (hL : Nat.card (lBar V₀ V hV L) = 3)
    (hrk : rk (wTil V₀ V hV L) = 6) : False := by
  obtain ⟨t, htM, -, -, -, hEq, hC⟩ := hc
  have h3 := three_le_rk_witness_of_card_three_rk_six
    (W := Vtil V₀ V hV) (A := Mbar D.M V₀ V hV)
    (L := lBar V₀ V hV L) (t := t) htM hC hL hrk
  rw [hEq] at h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
