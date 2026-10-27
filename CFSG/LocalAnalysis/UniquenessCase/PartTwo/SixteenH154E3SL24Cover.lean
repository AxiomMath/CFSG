module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_normalizer_cent_Z (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hnZ : ∀ z ∈ commSub ⊤ L ⊓ fixV L, n z = z) :
    ∃ l ∈ L, ∀ u ∈ commSub ⊤ L, n u = l u := by
  exact s16h_sl24_cover_normalizer_cent_Z_aux hW hrow hZ4 hn hnZ

theorem s16h_sl24_cover_sylow_fixed (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    {T : Subgroup (MulAut W)} (hT : T ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hT2 : IsPGroup 2 ↥T) :
    ∃ w ∈ commSub ⊤ L, w ∉ commSub ⊤ L ⊓ fixV L ∧ ∀ t ∈ T, t w = w := by
  exact s16h_sl24_cover_sylow_fixed_aux hW hrow hZ4 hT hT2

theorem s16h_sl24_cover_involution_rank (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W))) (hn2 : n ^ 2 = 1)
    (hnU : ∃ u ∈ commSub ⊤ L, n u ≠ u) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers n)) := by
  exact s16h_sl24_cover_involution_rank_aux hW hrow hZ4 hn hn2 hnU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
