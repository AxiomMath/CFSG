module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenIrreducibleQuotientCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Rechoice
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSp6Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}

omit [Finite W] in
private theorem s16k_hord_sp6 {H : Subgroup (MulAut W)} (hH : IsSpn H 6 1) :
    5 ≤ (Nat.card ↥H).factorization 2 := by
  have hHcard : Nat.card ↥H = 1451520 := s16c1610_card_of_isSpn_six hH
  rw [hHcard]
  norm_num [Nat.factorization]

theorem pRank_le_one_of_normalizes_sp6_quotient_rank_eight
    {A : Subgroup (MulAut W)}
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsSpn H 6 1)
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 8)
    (hAN : A ≤ Subgroup.normalizer (H : Set (MulAut W)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    CFSG.Open.pRank p A ≤ 1 := by
  have hmain := pRank_le_of_normalizes_irreducible_quotient_rank_eight hW
    (c8_isQuasisimple_of_isSpn hH) hcomm hirr hdim (s16k_hord_sp6 hH) hAN hp hp3
  have hHrank := s16k_pRank_aut_sp6 (X := ↥H) hH hp hp2
  rw [if_neg hp3] at hHrank
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
