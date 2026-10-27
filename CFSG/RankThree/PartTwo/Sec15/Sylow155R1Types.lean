module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.PGLModel

variable {G : Type} [Group G] [Finite G]

theorem res1At_iff {A : Subgroup G} {c : G} {L M : Subgroup G} :
    Res1At A c L M ↔ ∃ Yc, Res1AtOf A c L M Yc := by
  unfold Res1At Res1AtOf
  constructor
  · rintro ⟨h1, h2, h3, ⟨Yc, hY⟩, h5⟩
    exact ⟨Yc, h1, h2, h3, hY, h5⟩
  · rintro ⟨Yc, h1, h2, h3, hY, h5⟩
    exact ⟨h1, h2, h3, ⟨Yc, hY⟩, h5⟩

theorem odd_of_two_pow_mod_three {n : ℕ} (h : 2 ^ n % 3 = 2) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, Nat.pow_mod] at h
    norm_num at h
  · exact hn

theorem even_of_two_pow_mod_three {n : ℕ} (h : 2 ^ n % 3 = 1) : Even n := by
  rcases Nat.even_or_odd n with hn | ⟨k, rfl⟩
  · exact hn
  · rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h
    norm_num at h

theorem res1_type_cases {Y : Type} [Group Y] (h : Sec18.IsRankOneType189 Y) :
    Res1OddL2Type Y ∨ Res1OddL3Type Y ∨ Res1J1Type Y ∨ Res1SmallType Y ∨ Res1L2OddType Y ∨
      Res1MidType Y ∨ Res1OpenType Y := by
  rcases h with ⟨p, f, hp, hp3, hf, he⟩ | ⟨p, f, hp, hf, hmod, he⟩ | ⟨p, f, hp, hf, hmod, he⟩ |
    he
  · by_cases hp2 : p = 2
    · subst hp2
      rcases Nat.even_or_odd f with hev | hodd
      · by_cases hf2 : f = 2
        · subst hf2
          exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl he))))
        · obtain ⟨k, rfl⟩ := hev
          by_cases h4 : 4 ∣ k + k
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨k + k, by omega, h4, he⟩))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
              ⟨k + k, by omega, by omega, he⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hodd, he⟩))))
    · exact Or.inl ⟨p, f, hp, hp2, hp3, hf, he⟩
  · by_cases hp2 : p = 2
    · subst hp2
      have hodd := odd_of_two_pow_mod_three hmod
      by_cases hf1 : f = 1
      · subst hf1
        exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr he))))
      · obtain ⟨k, rfl⟩ := hodd
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr
          ⟨2 * k + 1, by omega, ⟨k, rfl⟩, he⟩))))))
    · exact Or.inr (Or.inl (Or.inl ⟨p, f, hp, hp2, hf, hmod, he⟩))
  · by_cases hp2 : p = 2
    · subst hp2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨f, by omega, even_of_two_pow_mod_three hmod, he⟩))))))
    · exact Or.inr (Or.inl (Or.inr ⟨p, f, hp, hp2, hf, hmod, he⟩))
  · exact Or.inr (Or.inr (Or.inl he))

end CFSG.RankThree.PartTwo.Sec15
