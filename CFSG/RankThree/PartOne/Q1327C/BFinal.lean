module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.RankThree.PartOne.Q1327C.BBase

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem seven_not_dvd_two_pow_add_one (f : ℕ) : ¬ 7 ∣ 2 ^ f + 1 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r : ℕ, r < 3 ∧ f = 3 * m + r :=
    ⟨f / 3, f % 3, Nat.mod_lt _ (by norm_num), by omega⟩
  have h8 : 2 ^ (3 * m) % 7 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  intro hd
  have h1 : 2 ^ (3 * m + r) % 7 = 2 ^ r % 7 := by
    rw [pow_add, Nat.mul_mod, h8, one_mul, Nat.mod_mod]
  interval_cases r <;> omega

end CFSG.RankThree.PartOne.Q1327C
