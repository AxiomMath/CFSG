module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOne
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_H5_dispatch_two
    (hJP : K_JonesParshallH1) {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hZ : commSub ⊤ L ⊓ fixV L ≠ ⊥)
    (hZ2 : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2)
    (hno : ¬ s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : s16h_BlockBound A L q 1 ∨ s16h_H5Fix A L q := by
  have hL3 : ∀ k : ℕ, k ≤ 3 →
      s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k →
      s16h_BlockBound A L q 1 ∨ s16h_H5Fix A L q := by
    intro k hk hsum
    have hk2 : k ≤ 2 := by
      by_contra h
      have hk3 : k = 3 := by omega
      exact hno (by simpa [hk3] using hsum)
    by_cases hq3 : q = 3
    · exact by simpa [hq3] using s16h_H5_row_L3_two hc hk2 hsum hZ2
    · exact Or.inl (s16h_H5_row_L3_one hc hk hsum hq hq2 (Or.inr (Or.inl ⟨hk2, hq3⟩)))
  have hA5 : s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) → False :=
    fun hr => hZ ((hJP W hc.elem L).1 (Or.inl hr))
  have hO42 : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 → False :=
    fun hr => hZ ((hJP W hc.elem L).1 (Or.inr (Or.inl hr)))
  have hO43 : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 → False :=
    fun hr => hZ ((hJP W hc.elem L).1 (Or.inr (Or.inr (Or.inl hr))))
  have hSt8 : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) →
      commSub ⊤ L ∈ irrSet L → False :=
    fun hr hirr => hZ ((hJP W hc.elem L).1 (Or.inr (Or.inr (Or.inr ⟨hr, hirr⟩))))
  rcases hc.conc.2.2 with h1 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h1).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · obtain ⟨-, hsum, -⟩ := h3
    rcases s16h_H5_thin_sum hc hsum with hr | hr
    · obtain ⟨k, hk, hsumk⟩ := (s16h_H5RowL3_iff L _ _).1 hr
      exact hL3 k hk hsumk
    · exact (hA5 hr).elim
  · obtain ⟨hirr, -, -, h135⟩ := h4
    rcases s16h_H5_thin_one hc h135 with hr | hr | hr | hr | hr | hr | hr
    · obtain ⟨k, hk, hsumk⟩ := (s16h_H5RowL3_iff L _ _).1 hr
      exact hL3 k hk hsumk
    · exact (hA5 hr).elim
    · by_cases hq3 : q = 3
      · exact Or.inr (by simpa [hq3] using s16h_H5_row_SL2_four_fix hc hr hZ2)
      · exact Or.inl (s16h_H5_row_SL2_four_one hc hr hq hq2 hq3)
    · by_cases hq37 : q = 3 ∨ q = 7
      · exact Or.inr (s16h_H5_row_SL2_eight_fix hc hr hZ2 hq37)
      · exact Or.inl (s16h_H5_row_SL2_eight_one hc hr hq hq2
          (fun h => hq37 (Or.inl h)) (fun h => hq37 (Or.inr h)))
    · exact (hO42 hr).elim
    · exact (hO43 hr).elim
    · exact (hSt8 hr hirr).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
