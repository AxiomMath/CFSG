module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA1AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedL3ABB1AA2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_two_involution_rank_normalizer
    (hW : ∀ w : W, w ^ 2 = 1)
    {A L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ A) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hconc : Conc4_136W A t L)
    (hcomp : IsComponentOf L A)
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1)
    (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hd2 : rk ↥(commSub ⊤ L ⊓ fixV L) = 2)
    {τ : MulAut W} (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1)
    (hτN : τ ∈ normalizer (L : Set (MulAut W))) :
    4 ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers τ)) := by
  by_cases hτC : τ ∈ centSub (commSub ⊤ L)
  · exact s16h_e3_l3_two_rank_normalizer_of_central hW ht ht2 ht1 htr hconc hcomp hthin hZ
      hL3 hd2 hτ hτ2 hτ1 hτN hτC
  · exact le_trans
      (s16h_e3_l3_two_rank_normalizer_of_not_central_aux hW ht ht2 ht1 htr hconc hcomp hthin hZ hL3
          hd2 hτ hτ2 hτ1 hτN hτC)
      (rk_mono (commSub_mono le_top le_rfl))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
