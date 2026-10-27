module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42DihC
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MMain
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

theorem ff79_4_2Pre_of' (hKL : FF79_4_2KLor) (hN : FF79LemmaN) (hQ : FF84.LemmaQ)
    (_h13 : FF79_1_3) (h14 : FF79_1_4) (h41 : FF79_4_1) : FF79_4_2Pre := by
  intro G _ _ b J B b₁ b₂ h
  obtain ⟨hC1, hsyl, hbL, hγK, hdisj⟩ := hKL G b J B b₁ b₂ h
  rcases hdisj with ⟨hK, hL⟩ | ⟨hK, hL⟩
  · have S := h.sit_main h14 h41 hsyl hbL hγK hK hL
    obtain ⟨hX1, hX2, hX3, -⟩ := h.lemma14 h14 h41
    refine ⟨hC1, hsyl, hK, hL, hbL, hγK, S.Lay_eq hN hQ, ?_, S.Δ_le_cenΛ hN hQ, ?_,
      S.Opp_eq hN hQ, m42_le_Opp hX1 hX2 hX3⟩
    · exact S.Λ_inf_Δ hN hQ
    · have := S.H_eq_cen_Lay hN hQ
      rwa [Set.pair_comm] at this
  · exact (m42_sym_false' hN hQ h hC1.1 (h.sit_sym h14 h41 hsyl hbL hγK hK hL)).elim

end CFSG.RankThree.PartTwo.Sec21.FF79
