module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5BridgeO4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5CntO4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_row_O4_two_rank [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
        Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  intro q hq hq2 E hE hEab
  obtain ⟨K, hKf, hKfin, hKchar, b, c, hKcard, hirr, D, hDN, hDab, hcard⟩ :=
    s16h_H5_bridge_omegaMinus4 hc h hq hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  rw [← hcard]
  exact s16h_natNorm_elemAbelian_le_omegaMinus4 (K := K) (a := 2)
    ⟨by norm_num, by norm_num⟩ hKcard hirr hq hq2 hDN hDab

theorem s16h_H5_row_O4_two [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2) :
    s16h_H5Block A L :=
  s16h_H5_block_of_autSub (s16h_H5_row_O4_two_rank hc h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
