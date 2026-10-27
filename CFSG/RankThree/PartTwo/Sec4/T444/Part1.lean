module

public import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem rank3II_4_44_1_of (h450 : Item4_50) (h452 : Item4_52) (h453 : Item4_53) :
    Item4_44_1 := by
  intro G _ _ A M h hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, hL, hQL, hLQ, hLM⟩ := h450 G A M h (Or.inl hne)
  have hLC := h452 G A M h (Or.inl hne) L hL hQL hLQ hLM
  obtain ⟨S, hS⟩ := exists_sylow_le_normalizer h.isE27.isPGroup
    (not_three_dvd_card_inSubgroup_pPrimeCore M) h.le_normalizer_inSubgroup 2
  exact ⟨L, hLC, S, h453 G A M h hne L hL hQL hLQ hLM S hS⟩

end CFSG.RankThree.PartTwo.Sec4
