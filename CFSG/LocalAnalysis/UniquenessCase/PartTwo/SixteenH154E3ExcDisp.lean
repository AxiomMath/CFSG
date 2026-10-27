module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowA5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSL8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowSt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_exc_dispatch
    (hJP : K_JonesParshallH1) {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hZ : commSub ⊤ L ⊓ fixV L = ⊥) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hn1 : ¬ s16h_BlockBound A L q 1) (hnF : ¬ s16h_H5Fix A L q) :
    (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨ s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
  have hZ2 : Nat.card ↥(commSub ⊤ L ⊓ fixV L) ≤ 2 := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  have hL3 : ∀ k : ℕ, k ≤ 3 →
      s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro k hk hsum
    by_cases hk3 : k = 3
    ·
      have hq37 : q = 3 ∨ q = 7 := by
        by_contra h
        have hq3 : q ≠ 3 := fun h3 => h (Or.inl h3)
        have hq7 : q ≠ 7 := fun h7 => h (Or.inr h7)
        exact hn1 (s16h_H5_row_L3_one hc hk hsum hq hq2 (Or.inl ⟨hq3, hq7⟩))
      refine Or.inr ⟨hq37, ?_⟩
      rw [hk3] at hsum
      simpa [hZ] using hsum
    · have hk2 : k ≤ 2 := by omega
      by_cases hq3 : q = 3
      ·
        exfalso
        exact (s16h_H5_row_L3_two hc hk2 hsum hZ2).elim
          (fun hb => hn1 (by simpa [hq3] using hb))
          (fun hf => hnF (by simpa [hq3] using hf))
      · exfalso
        exact hn1 (s16h_H5_row_L3_one hc hk hsum hq hq2 (Or.inr (Or.inl ⟨hk2, hq3⟩)))
  have hA5 : ∀ k : ℕ, k ≤ 3 →
      s16h_H5A5Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro k hk hsum
    by_cases hk1 : k ≤ 1
    ·
      exfalso
      exact hn1 (s16h_H5_row_A5_one hc hk hsum hq hq2 (Or.inr hk1))
    · have hk23 : k = 2 ∨ k = 3 := by omega
      by_cases hq3 : q = 3
      ·
        refine Or.inl ⟨hq3, ?_⟩
        rcases hk23 with hk2 | hk3
        · left
          rw [hk2] at hsum
          simpa [hZ] using hsum
        · right
          rw [hk3] at hsum
          simpa [hZ] using hsum
      · exfalso
        exact hn1 (s16h_H5_row_A5_one hc hk hsum hq hq2 (Or.inl hq3))
  have hSL4 : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro hr
    by_cases hq3 : q = 3
    · exfalso
      exact hnF (by simpa [hq3] using s16h_H5_row_SL2_four_fix hc hr hZ2)
    · exfalso
      exact hn1 (s16h_H5_row_SL2_four_one hc hr hq hq2 hq3)
  have hSL8 : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro hr
    by_cases hq37 : q = 3 ∨ q = 7
    · exfalso
      exact hnF (s16h_H5_row_SL2_eight_fix hc hr hZ2 hq37)
    · exfalso
      have hq3 : q ≠ 3 := fun h3 => hq37 (Or.inl h3)
      have hq7 : q ≠ 7 := fun h7 => hq37 (Or.inr h7)
      exact hn1 (s16h_H5_row_SL2_eight_one hc hr hq hq2 hq3 hq7)
  have hO42 : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro hr
    by_cases hq3 : q = 3
    · exfalso
      exact hnF (by simpa [hq3] using s16h_H5_row_O4_two_fix hc hr hZ)
    · exfalso
      exact hn1 (s16h_H5_row_O4_two_one hc hr hq hq2 hq3)
  have hO43 : s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro hr
    by_cases hq37 : q = 3 ∨ q = 7
    · exfalso
      exact hnF (s16h_H5_row_O4_three_fix hc hr hZ hq37)
    · exfalso
      have hq3 : q ≠ 3 := fun h3 => hq37 (Or.inl h3)
      have hq7 : q ≠ 7 := fun h7 => hq37 (Or.inr h7)
      exact hn1 (s16h_H5_row_O4_three_one hc hr hq hq2 hq3 hq7)
  have hSt8 : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) →
      (q = 3 ∧ (s16h_H5A5Sum L (commSub ⊤ L) ⊥ 2 ∨
        s16h_H5A5Sum L (commSub ⊤ L) ⊥ 3)) ∨
      ((q = 3 ∨ q = 7) ∧ s16h_H5L3Sum L (commSub ⊤ L) ⊥ 3) := by
    intro hr
    exfalso
    exact hn1 (s16h_H5_row_St8_one hc hr hq hq2)
  rcases hc.conc.2.2 with h1 | h2 | h3 | h4
  · exact (s16h_H5_not_pgroup hc h1).elim
  · exact (s16h_H5_not_tensor hc h2).elim
  · obtain ⟨-, hsum, -⟩ := h3
    rcases s16h_H5_thin_sum hc hsum with hr | hr
    · obtain ⟨k, hk, hsumk⟩ := (s16h_H5RowL3_iff L _ _).1 hr
      exact hL3 k hk hsumk
    · obtain ⟨k, hk, hsumk⟩ := (s16h_H5RowA5_iff L _ _).1 hr
      exact hA5 k hk hsumk
  · obtain ⟨-, -, -, h135⟩ := h4
    rcases s16h_H5_thin_one hc h135 with hr | hr | hr | hr | hr | hr | hr
    · obtain ⟨k, hk, hsumk⟩ := (s16h_H5RowL3_iff L _ _).1 hr
      exact hL3 k hk hsumk
    · obtain ⟨k, hk, hsumk⟩ := (s16h_H5RowA5_iff L _ _).1 hr
      exact hA5 k hk hsumk
    · exact hSL4 hr
    · exact hSL8 hr
    · exact hO42 hr
    · exact hO43 hr
    · exact hSt8 hr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
