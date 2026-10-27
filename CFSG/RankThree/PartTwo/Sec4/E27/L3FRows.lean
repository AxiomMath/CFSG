module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3F
public import CFSG.RankThree.PartTwo.Sec4.E27.Assembly

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem two_pow_mod_three_of_even {n : ℕ} (hev : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨a, rfl⟩ := hev
  rw [← two_mul, pow_mul]
  norm_num [Nat.pow_mod]

theorem two_pow_mod_three_of_odd {n : ℕ} (hodd : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨a, rfl⟩ := hodd
  rw [pow_succ, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

section Rows


theorem seitz27L3F_holds : Seitz27L3F := by
  intro n hn4 hn6 h3n X _ _ hX
  have hn9 : 9 ≤ n := by
    obtain ⟨a, rfl⟩ := h3n
    omega
  rcases hX with ⟨hmod, ⟨φ⟩⟩ | ⟨hmod, ⟨φ⟩⟩
  · have hev : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · have := two_pow_mod_three_of_odd h
        omega
    have hn12 : 12 ≤ n := by
      obtain ⟨a, rfl⟩ := h3n
      obtain ⟨b, hb⟩ := hev
      omega
    exact seitz27_of_mulEquiv φ (seitz27_l3pi hn12 h3n hev)
  · have hodd : Odd n := by
      rcases Nat.even_or_odd n with h | h
      · have := two_pow_mod_three_of_even h
        omega
      · exact h
    exact seitz27_of_mulEquiv φ (seitz27_u3pi hn9 h3n hodd)

end Rows

end CFSG.RankThree.PartTwo.Sec4.E27
