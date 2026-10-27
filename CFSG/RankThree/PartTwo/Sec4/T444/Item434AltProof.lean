module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Alt
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltNineTwelve

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

section Families


theorem item434AltLie : Item434AltLie := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨n, hn, ⟨e⟩⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact (Item434Alt.false_of_alt_six hc e).elim
  · exact (Item434Alt.false_of_alt_eight hc e).elim

theorem item434AltSeven : Item434AltSeven := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨n, hn, ⟨e⟩⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn
  exact (Item434Alt.false_of_alt_seven hc e).elim

theorem item434AltNine : Item434AltNine := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨n, hn, ⟨e⟩⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn
  exact (Item434Alt.false_of_alt_nine hc e).elim

theorem item434AltTenEleven : Item434AltTenEleven := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨n, hn, ⟨e⟩⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact (Item434Alt.false_of_alt_ten hc e).elim
  · exact (Item434Alt.false_of_alt_eleven hc e).elim

theorem item434AltTwelve : Item434AltTwelve := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨n, hn, ⟨e⟩⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  subst hn
  exact (Item434Alt.false_of_alt_twelve hc e).elim

theorem item434Alt : Item434Alt :=
  item434Alt_of item434AltLie item434AltSeven item434AltNine item434AltTenEleven item434AltTwelve

end Families

end CFSG.RankThree.PartTwo.Sec4
