module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_thin_one
    [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {m : ℕ}
    (h : Conc4_135 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) m) :
    s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
      s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
      s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
      s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
      s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) := by
  rcases hc.conc.2.2 with h133 | htensor | h3 | h4
  · exact (s16h_H5_not_pgroup hc h133).elim
  · exact (s16h_H5_not_tensor hc htensor).elim
  · obtain ⟨-, hsum, -⟩ := h3
    rcases s16h_H5_thin_sum hc hsum with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
  · obtain ⟨-, -, -, h135⟩ := h4
    exact s16h_H5_thin_one_case4 hc h135

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
