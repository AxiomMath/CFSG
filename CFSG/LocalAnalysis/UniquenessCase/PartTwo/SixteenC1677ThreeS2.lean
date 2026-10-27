module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeS1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeS2Z7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s2_choice {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h164 : R16_4 D) (hs : 1 < s15 D.M V₀ V hV L)
    (h163 : Concl163F D V₀ V hV L) : Choice168F D V₀ V hV := by
  obtain ⟨hs2, hγ⟩ := h164 V₀ V L hV c.setting c.conc hs
  rcases hγ with hγ3 | h | h | h
  · rcases h163 with h162 | h | h | h | h | h | h | h | h | h | h | h | h
    · rcases h162 with h153 | h | h | h | h | h | h | h | h | h
      · rcases h153 with h | h | h
        · exact absurd h.2.2.2.2.1 (by omega)
        · exact Choice168F.of_final c (Final168F.of_case167_2 (s168e3_s2_153_2 c hs2 hγ3 h))
        · exact Choice168F.of_final c (Final168F.of_case167_3 (s168e3_s2_153_3 c hs2 h))
      · exact (s16e_s2_162_1 D h hγ3).elim
      · exact absurd h.1 (by omega)
      · obtain ⟨hc, hrk, -⟩ := h
        exact (s16e_s2_false_of_odd D (by rw [hc.2]; decide) (by omega) hγ3).elim
      · obtain ⟨hP, hrk, -⟩ := h
        exact (s16e_s2_false_of_odd D (by rw [hP.2.1]; decide) (by omega) hγ3).elim
      · obtain ⟨⟨r, hE, hrk⟩, -⟩ := h
        have hr := s16e_one_le_of_elemAbelianOfRank c.ne hE
        exact (s16e_s2_false_of_odd D (s16e_odd_card_of_elemAbelianOfRank hE (by decide))
          (by omega) hγ3).elim
      · exact absurd h.2.2.1 (by omega)
      · exact absurd h.2.2 (by omega)
      · exact (s16e_s2_162_8 D h hγ3).elim
      · exact absurd h.2.2.1 (by omega)
    · exact absurd h.2.1 (by omega)
    · exact absurd h.2.2 (by omega)
    · exact (s16e_s2_163_3 D h hγ3).elim
    · exact (s16e_s2_163_4 D h hγ3).elim
    · exact (s16e_s2_163_5 D h hγ3).elim
    · exact absurd h.2.2.1 (by omega)
    · exact Choice168F.of_final c (Final168F.of_case168_7 h)
    · exact absurd h.2.2.1 (by omega)
    · obtain ⟨hc, hrk, -⟩ := h
      exact (s16e_s2_false_of_odd D (by rw [hc.2]; decide) (by omega) hγ3).elim
    · obtain ⟨hE, hrk⟩ := h
      exact (s16e_s2_false_of_odd D (s16e_odd_card_of_elemAbelianOfRank hE (by decide))
        (by omega) hγ3).elim
    · obtain ⟨r, hE, hrk⟩ := h
      have hr := s16e_one_le_of_elemAbelianOfRank c.ne hE
      exact (s16e_s2_false_of_odd D (s16e_odd_card_of_elemAbelianOfRank hE (by decide))
        (by omega) hγ3).elim
    · have hsig := s168e3_s2_163_12 c hs2 h
      obtain ⟨hc, hrk, -⟩ := h
      exact Choice168F.of_final c (Final168F.of_case168_11 ⟨hc, hrk, hs2, hsig⟩)
  · exact Choice168F.of_final c (Final168F.of_case168_6 ⟨h.2.2.2, h.1, hs2, h.2.1⟩)
  · exact Choice168F.of_final c
      (Final168F.of_case168_9 ⟨h.2.2.2.2, h.1, hs2, h.2.1, h.2.2.1⟩)
  · obtain ⟨p, hp, hc, hrk, hsig, -, hF⟩ := h
    exact Choice168F.of_final c (Final168F.of_case168_10 ⟨p, hp, hc, hrk, hs2, hsig, hF⟩)

theorem s168e3_choice_of_r16_3FE
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h163 : R16_3FE D) (h164 : R16_4 D) (h165 : R16_5 D)
    (h6 : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V),
      S168e3Ctx D V₀ V L hV → Case163_6 D V₀ V hV L → False) :
    Choice168F D V₀ V hV := by
  obtain ⟨L', hset', hne', hconc', hclass'⟩ := h163 V₀ V L hV c.setting c.ne c.conc
  let c' : S168e3Ctx D V₀ V L' hV := ⟨c.std, hset', hne', hconc'⟩
  by_cases hs : s15 D.M V₀ V hV L' = 1
  · exact s168e3_s1_choice_of_case163_6_false c' hSchur h164 h165
      (h6 V₀ V L' hV c') hs hclass'
  · have := Om8Excl.one_le_s15 D.M V₀ V hV L'
    exact s168e3_s2_choice c' h164 (by omega) hclass'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
