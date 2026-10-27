module

public import CFSG.Quasithin.Vol2.Ch10SecD12T
public import CFSG.Quasithin.Vol2.Ch10SecD12G
public import CFSG.Quasithin.Vol2.Ch10SecD12P

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

theorem eq_two_or_lt_of_one_lt {w : ℕ∞} (hw : 1 < w) : w = 2 ∨ 2 < w := by
  have h2 : (2 : ℕ∞) ≤ w := by
    have := (ENat.natCast_add_one_le_iff (m := 1)).mpr (by exact_mod_cast hw)
    exact_mod_cast this
  rcases eq_or_lt_of_le h2 with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

theorem stmt10_2_12_of (hL2 : Fact12L2) (hA5 : Fact12A5) (hO4 : Fact12O4) (hWW : Fact12WW)
    (hSz : Fact12Sz) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6) (h1011 : Stmt10_1_1)
    (h1012 : Stmt10_1_2) (h1013 : Stmt10_1_3) (h1027 : Stmt10_2_7) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h10211 : Stmt10_2_11) : Stmt10_2_12 := by
  intro G _ _ T L I h
  have key : ∀ {m a0 r0 : ℕ} (j : ℕ), Data10212 T L I m a0 r0 → r0 + 2 ≤ m → j + 2 ≤ m →
      j + a0 < m → (j : ℕ∞) < E3.wParam T (fsuVM T L I) := fun j hD hr hj hja =>
    lt_wParam hD (Or.inl (wParam_pos hD hr h331 h37 h38 h1029 h10210 h)) hj hja h331 h37 h38
      h1013 h1029 h10210 h
  by_cases h3 : Case10_1_1Three T L I
  · rcases eq_two_or_lt_of_one_lt
      (one_lt_wParam_three h331 h37 h38 hI16 h1013 h1029 h10210 h10211 h h3) with h2 | h2
    · exact Or.inr (Or.inl ⟨h2, h3⟩)
    · exact Or.inl h2
  by_cases h1 : ∃ n, Case10_1_1One T L I n
  · obtain ⟨n, hn1⟩ := h1
    have hD := data_one hL2 h37 h38 hI16 h hn1
    have hn : 1 < n := hn1.1
    by_cases hn2 : n = 2
    · subst hn2
      rcases eq_two_or_lt_of_one_lt (key 1 hD (by norm_num) (by norm_num) (by norm_num))
        with h2 | h2
      · exact Or.inr (Or.inr ⟨h2, hn1⟩)
      · exact Or.inl h2
    · have h2 := key 2 hD (by omega) (by omega) (by omega)
      exact Or.inl (by exact_mod_cast h2)
  have hc : fsuCVM T L I = ⊥ := (h1012 G T L I h).2.2.2.2.2.2.1 (by
    rintro (h1' | h3')
    · exact h1 h1'
    · exact h3 h3')
  rcases (h1011 G T L I h).2.2.2 with h1' | h2 | h3' | ⟨n, hn4⟩ | h5 | h6 | h7
  · exact absurd h1' h1
  · have h2' := key 2 (data_two hA5 h37 h38 h h2 hc) (by norm_num) (by norm_num) (by norm_num)
    exact Or.inl (by exact_mod_cast h2')
  · exact absurd h3' h3
  · have hn : 1 < n := hn4.1
    have h2' := key 2 (data_four hO4 h37 h38 h hn4 hc) (by omega) (by omega) (by omega)
    exact Or.inl (by exact_mod_cast h2')
  · have h2' := key 2 (data_five hWW h37 h38 h h5 hc) (by norm_num) (by norm_num) (by norm_num)
    exact Or.inl (by exact_mod_cast h2')
  · exact absurd h6 (h1027 G T L I h).1
  · obtain ⟨n, hn, hD⟩ := data_seven hSz h37 h38 h h7 hc
    have h2' := key 2 hD (by omega) (by omega) (by omega)
    exact Or.inl (by exact_mod_cast h2')

end CFSG.Quasithin.Vol2.Ch10.SecD
