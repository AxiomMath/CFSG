module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24CoverCB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4BA1BAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_involution_rank_aux (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    {n : MulAut W} (hn : n ∈ Subgroup.normalizer (L : Set (MulAut W))) (hn2 : n ^ 2 = 1)
    (hnU : ∃ u ∈ commSub ⊤ L, n u ≠ u) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers n)) := by
  obtain ⟨K, hKf, hKfin, hKcard, π, β, hπs, hβs, hβk, hβe⟩ :=
    s16h_sl24_cover_coord (L := L) (U := commSub ⊤ L)
      (Z := commSub ⊤ L ⊓ fixV L) hrow
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨s, hsN, hs2, hs1, hrk⟩ :=
    s16h_sl24_cover_transfer (W := W) hW hKcard hπs hβs hβk hβe hn hn2 hnU
  exact le_trans (s16h_sl4_natNorm_involution hKcard hsN hs2 hs1) hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
