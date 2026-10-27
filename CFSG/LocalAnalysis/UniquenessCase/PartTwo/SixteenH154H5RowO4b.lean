module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5BridgeO4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5CntO4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_row_O4_b_bound [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  intro q hq hq2 E hE hEab
  obtain ⟨K, hF, hFin, hCh, b, c, hK, hirr, D, hD, hDab, hcard⟩ :=
    s16h_H5_bridge_omegaMinus4 hc h hq hq2 hE hEab
  letI := hF
  letI := hFin
  haveI := hCh
  have hle := s16h_natNorm_elemAbelian_le_omegaMinus4 (K := K) (a := 3) ⟨by norm_num, le_rfl⟩ hK
    hirr hq hq2 hD hDab
  rw [← hcard]
  exact hle

theorem s16h_H5_row_O4_three [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    s16h_H5Block A L :=
  s16h_H5_block_of_autSub (A := A) (L := L) (s16h_H5_row_O4_b_bound hc h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
