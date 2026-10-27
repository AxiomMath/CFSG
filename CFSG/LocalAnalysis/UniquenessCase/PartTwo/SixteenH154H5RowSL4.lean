module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowSL4A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5BridgeSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_row_SL2_four_bridge [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Subgroup (MulAut W)}
    (hE : E ≤ A ⊓ normalizer (L : Set (MulAut W))) (hEab : IsElemAbelian q E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = 4)
      (D : Subgroup (MulAut (StdMod (Fin 2) K))),
      D ≤ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧
      IsElemAbelian q D ∧
      Nat.card D = Nat.card ↥(autSub E (commSub ⊤ L)) := by
  obtain ⟨K, hF, hFin, hK, D, hD, hDab, hcard⟩ :=
    s16h_H5_bridge_statedSL2 hc h hq hq2 hE hEab
  exact ⟨K, hF, hFin, by simpa using hK, D, hD, hDab, hcard⟩

theorem s16h_H5_row_SL2_four_rank [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q ^ 2 := by
  intro q hq hq2 E hE hEab
  obtain ⟨K, hKf, hKfin, hKcard, D, hDN, hD, hcard⟩ :=
    s16h_H5_row_SL2_four_bridge hc h hq hq2 hE hEab
  letI : Field K := hKf
  letI : Finite K := hKfin
  rw [← hcard]
  exact s16h_H5_natNorm_statedSL_two_four_elemAbelian (K := K) (D := D) hKcard hq hq2 hDN hD

theorem s16h_H5_row_SL2_four [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2) :
    s16h_H5Block A L :=
  s16h_H5_block_of_autSub (A := A) (L := L) (s16h_H5_row_SL2_four_rank hc h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
