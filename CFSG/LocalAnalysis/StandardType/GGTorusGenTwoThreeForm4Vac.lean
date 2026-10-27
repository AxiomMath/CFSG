module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwoThreeNarrow22Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TBForm4RestTwoThree_holds : GGL48TBForm4RestTwoThree := by
  intro p lab hp hlab hs hv h0 hA hT hB hE hTA hSp hDp hDm hD3 hX hE6 hU4 hX2 hO
  exfalso
  obtain ⟨t, l, n⟩ := lab
  have splitU : ∀ (u : LargeEvenLieTag) {l n : ℕ}, LargeEvenUntwisted u →
      LargeEvenSplit p ⟨u, l, n⟩ → p ∣ 2 ^ n - 1 ∨ n = 1 ∧ p = 3 := by
    intro u l n hu hs
    rcases hs with ⟨-, hd⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact Or.inl hd
    · exact absurd hu h
    · rcases h with h | h
      · have h' : u = .twD := h
        rw [h'] at hu
        exact absurd hu (by simp [LargeEvenUntwisted])
      · have h' : u = .triD4 := h
        rw [h'] at hu
        exact absurd hu (by simp [LargeEvenUntwisted])
    · exact Or.inr h
  cases t
  ·
    obtain ⟨-, hl, -⟩ := hlab
    rcases Nat.lt_or_ge l 3 with h3 | h3
    · interval_cases l
      · exact hv (by simp [GGL48TableBVacLabel, GGLinearTwoLabel])
      · exact hv (by simp [GGL48TableBVacLabel])
    · rcases splitU .A trivial hs with hd | ⟨hn1, hp3⟩
      · exact hA ⟨rfl, h3, hd⟩
      · exact hTA ⟨rfl, h3, hn1, hp3⟩
  ·
    obtain ⟨-, hl, -⟩ := hlab
    have hd : p ∣ 2 ^ n + 1 := by
      rcases hs with ⟨h, -⟩ | ⟨-, -, hd⟩ | ⟨h, -⟩ | ⟨hn1, hp3⟩
      · exact absurd h (by simp [LargeEvenUntwisted])
      · exact hd
      · rcases h with h | h <;> cases h
      · have hn1' : n = 1 := hn1
        rw [hn1', hp3]
        norm_num
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · interval_cases l
      · exact hv (by simp [GGL48TableBVacLabel, GGLinearTwoLabel])
      · exact hU4 ⟨Or.inl rfl, rfl, hd⟩
    · by_cases hpl : p ∣ l + 1
      · exact h0 (Or.inl ⟨rfl, hpl, hd⟩)
      · exact hT ⟨rfl, h4, hd, hpl⟩
  ·
    rcases splitU .B trivial hs with hd | ⟨hn1, hp3⟩
    · exact hB ⟨Or.inl rfl, hd⟩
    · exact hSp ⟨hp3, hn1, Or.inl rfl⟩
  ·
    rcases splitU .C trivial hs with hd | ⟨hn1, hp3⟩
    · exact hB ⟨Or.inr rfl, hd⟩
    · exact hSp ⟨hp3, hn1, Or.inr rfl⟩
  ·
    obtain ⟨-, hl⟩ := hlab
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · interval_cases l
      rcases splitU .D trivial hs with hd | ⟨hn1, hp3⟩
      · exact hD3 ⟨rfl, rfl, hd⟩
      · exact hv (by simp [GGL48TableBVacLabel, StdSubRestThree.GGTwoThreeSmallLabel,
          hp3, hn1])
    · rcases splitU .D trivial hs with hd | ⟨hn1, hp3⟩
      · exact hO ⟨Or.inl rfl, h4, Or.inl hd⟩
      · exact hDp ⟨h4, rfl, hn1, hp3⟩
  ·
    obtain ⟨-, hl⟩ := hlab
    rcases hs with ⟨h, -⟩ | ⟨-, -, hd⟩ | ⟨-, hd⟩ | ⟨hn1, hp3⟩
    · exact h
    · rcases Nat.lt_or_ge l 4 with h4 | h4
      · interval_cases l
        · exact hv (by simp [GGL48TableBVacLabel, GGLinearTwoLabel])
        · exact hU4 ⟨Or.inr rfl, rfl, hd⟩
      · exact hO ⟨Or.inr rfl, h4, Or.inr hd⟩
    · rcases Nat.lt_or_ge l 4 with h4 | h4
      · interval_cases l
        · exact hv (by simp [GGL48TableBVacLabel, GGLinearTwoLabel])
        · exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
            GGStdSubSmallVacLabel, GGTableBTwDThreeLabel, hd])
      · exact hO ⟨Or.inr rfl, h4, Or.inl hd⟩
    · have hd : p ∣ 2 ^ n + 1 := by
        have hn1' : n = 1 := hn1
        rw [hn1', hp3]
        norm_num
      rcases Nat.lt_or_ge l 4 with h4 | h4
      · interval_cases l
        · exact hv (by simp [GGL48TableBVacLabel, GGLinearTwoLabel])
        · exact hU4 ⟨Or.inr rfl, rfl, hd⟩
      · exact hDm ⟨h4, rfl, hn1, hp3⟩
  ·
    rcases splitU .E6 trivial hs with hd | ⟨hn1, hp3⟩
    · exact hE6 ⟨rfl, hd⟩
    · exact hX2 ⟨Or.inl rfl, hn1, hp3⟩
  ·
    rcases splitU .E7 trivial hs with hd | ⟨hn1, hp3⟩
    · exact hX ⟨Or.inl rfl, hd⟩
    · exact hX2 ⟨Or.inr (Or.inl rfl), hn1, hp3⟩
  ·
    rcases splitU .E8 trivial hs with hd | ⟨hn1, hp3⟩
    · exact hX ⟨Or.inr (Or.inl rfl), hd⟩
    · exact hX2 ⟨Or.inr (Or.inr (Or.inl rfl)), hn1, hp3⟩
  ·
    rcases splitU .F4 trivial hs with hd | ⟨hn1, hp3⟩
    · exact hX ⟨Or.inr (Or.inr rfl), hd⟩
    · exact hX2 ⟨Or.inr (Or.inr (Or.inr rfl)), hn1, hp3⟩
  ·
    obtain ⟨hn, -⟩ := hlab
    have hn' : 1 ≤ n := hn
    have key : p ∣ 2 ^ n + 1 → False := by
      intro hd
      have hpne2 : p ≠ 2 := by
        rintro rfl
        have h2n : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
        have h1 : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right h2n).mp hd
        norm_num at h1
      by_cases hp3 : p = 3
      · subst hp3
        exact h0 (Or.inr ⟨rfl, rfl, hd⟩)
      · have hp5 : 5 ≤ p := by
          by_contra h5
          have hp2le : 2 ≤ p := hp.two_le
          have hlt : p < 5 := by omega
          interval_cases p
          · exact hpne2 rfl
          · exact hp3 rfl
          · norm_num at hp
        exact hE ⟨rfl, hp5, hd⟩
    rcases hs with ⟨h, -⟩ | ⟨-, -, hd⟩ | ⟨h, -⟩ | ⟨hn1, hp3⟩
    · exact h
    · exact key hd
    · rcases h with h | h <;> cases h
    · exact key (by
        have hn1' : n = 1 := hn1
        rw [hn1', hp3]
        norm_num)
  ·
    exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
      TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel])
  ·
    exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel, GGStdSubSmallVacLabel])
  ·
    exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel, GGStdSubSmallVacLabel])
  ·
    by_cases hp3 : p = 3
    · exact hv (Or.inr (Or.inl ⟨rfl, hp3⟩))
    · exact hv (Or.inl (Or.inl (Or.inr (Or.inr ⟨rfl, hp3⟩))))
  ·
    obtain ⟨-, -, hn1⟩ := hlab
    rcases hs with ⟨-, hd⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp3⟩
    · rw [hn1] at hd
      exact hp.ne_one (Nat.dvd_one.mp hd)
    · exact h trivial
    · rcases h with h | h <;> cases h
    · exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
        GGStdSubSmallVacLabel, GGB2derThreeLabel, hp3])
  ·
    exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel,
      TableBExcSmallRanks.GGTableBExcSmallRanksDoneLabel])
  ·
    exact hv (by simp [GGL48TableBVacLabel, GGCorFourTwoSmallLabel])

end CFSG.StandardType
