module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_row_L3_one {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {k : ℕ} (hk : k ≤ 3)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hq37 : (q ≠ 3 ∧ q ≠ 7) ∨ (k ≤ 2 ∧ q ≠ 3) ∨ k ≤ 1) : s16h_BlockBound A L q 1 :=
  s16h_H5_row_L3_block_of_autSub_one (fun E hE hEab =>
    s16h_H5_row_L3_one_rank hc hk h hq hq2 hq37 E hE hEab)

theorem s16h_H5_row_L3_two {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {k : ℕ} (hk : k ≤ 2)
    (h : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    (hZ : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2) :
    s16h_BlockBound A L 3 1 ∨ s16h_H5Fix A L 3 := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · refine Or.inl (s16h_H5_row_L3_one hc (by omega) h (by norm_num) (by norm_num) ?_)
    exact Or.inr (Or.inr (by omega))
  · have hk2' : k = 2 := by omega
    subst hk2'
    exact Or.inr (s16h_H5_row_L3_two_fix hc h hZ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
