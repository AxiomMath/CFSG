module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeStd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeR153
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeR1532
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeR1531
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeElem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeCycRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeOm4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeD5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s1_choice_of_case163_6_false
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h164 : R16_4 D) (h165 : R16_5 D)
    (h6 : Case163_6 D V₀ V hV L → False) (hs : s15 D.M V₀ V hV L = 1)
    (h163 : Concl163F D V₀ V hV L) : Choice168F D V₀ V hV := by
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hrkT : ∀ n : ℕ, rk ↥(wTil V₀ V hV L) = n → rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = n := by
    intro n hn
    rw [← hwT]
    exact hn
  rcases h163 with h162 | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h162 with h153 | h | h | h | h | h | h | h | h | h
    · rcases h153 with h | h | h
      · exact Choice168F.of_final c (Final168F.of_case167_1 (s168e3_row153_1 c h))
      · exact (s168e3_row153_2 c hs h).elim
      · exact (s168e3_row153_3 c hs h).elim
    · exact absurd h.2 (by omega)
    · rcases s168e3_row162_2 c hSchur h with h' | h'
      · exact Choice168F.of_final c (Final168F.of_case168_1 h')
      · exact Choice168F.of_final c (Final168F.of_case168_2Star h')
    · exact absurd h.2.2 (by omega)
    · obtain ⟨hP, hrk, -⟩ := h
      exact Choice168F.of_final c (Final168F.of_case168_3
        ⟨hP, hrkT _ hrk, s168e3_sig_eq_three_of_p1p2 c hs hP hrk⟩)
    · obtain ⟨⟨r, hE, hrk⟩, -⟩ := h
      have hr := s16e_one_le_of_elemAbelianOfRank c.ne hE
      by_cases hr1 : r = 1
      · subst hr1
        exact s168e3_row_z3_four c hs hE (by omega)
      · exact Choice168F.of_final c (Final168F.of_case168_4
          (s168e3_s1_case4_of_elem c hs (Or.inl rfl) (by omega) hE
            (by rw [s16c1610_dParam_three]; omega)))
    · exact Choice168F.of_final c (Final168F.of_case167_4 (s168e3_row162_6 c h))
    · exact Choice168F.of_final c (s168e3_row162_7 c h)
    · exact absurd h.2 (by omega)
    · exact Choice168F.of_final c (Final168F.of_case167_8 (s168e3_row162_9 c h))
  · exact absurd h.2.2 (by omega)
  · exact Choice168F.of_final c (Final168F.of_case167_6 (s168e3_row163_2 c h165 h))
  · exact absurd h.2.2.1 (by omega)
  · exact absurd h.2.2 (by omega)
  · exact absurd h.2 (by omega)
  · exact (h6 h).elim
  · exact Choice168F.of_final c (Final168F.of_case168_7 (s168e3_row163_7 h))
  · exact Choice168F.of_final c (Final168F.of_case167_7F (s168e3_row163_8F c h))
  · exact absurd h.2.2 (by omega)
  · exact Choice168F.of_final c (Final168F.of_case168_8 (s168e3_row163_10 c h164 hs h))
  · obtain ⟨r, hE, hrk⟩ := h
    have hr := s16e_one_le_of_elemAbelianOfRank c.ne hE
    by_cases hr1 : r = 1
    · subst hr1
      exact s168e3_row_z7_six c hs hE (by omega)
    · exact Choice168F.of_final c (Final168F.of_case168_4
        (s168e3_s1_case4_of_elem c hs (Or.inr rfl) (by omega) hE
          (by rw [s16c1610_dParam_seven]; omega)))
  · exact absurd h.2.2 (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
