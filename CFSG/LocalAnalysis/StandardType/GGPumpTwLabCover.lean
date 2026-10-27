module

public import CFSG.LocalAnalysis.StandardType.GGKacK1

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l04fHL7_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rw [pow_succ]
    have hpos : 0 < 2 ^ n := pow_pos (by norm_num) n
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      refine ⟨2 * k + 1, by omega⟩
    · left
      refine ⟨2 * k - 1, by omega⟩

theorem ggPumpTwLab_cover (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) :
    GGKacGenericClA lab 3 ∨ (GGKacGenericClC lab 3 ∨ GGKacGenericClD lab 3) ∨
      ((lab.tag = .A ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1)) ∨
      (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∨
      (lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
        lab.tag = .twF4der ∨ lab.tag = .B2der) := by
  obtain ⟨tag, rank, n⟩ := lab
  have h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := l04fHL7_three_dvd n
  cases tag
  ·
    by_cases hcond : 3 ∣ rank + 1 ∧ 3 ∣ 2 ^ n - 1
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, hcond.1, hcond.2⟩)))
    · have hgen : GGKacGenericCl ⟨.A, rank, n⟩ 3 :=
        ⟨Nat.prime_three, by norm_num, h3, Or.inl rfl,
          (by intro h; exact hcond h.2),
          (by intro h; cases h.1)⟩
      rcases ggKacGenericCl_lanes hlab hgen with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
  ·
    by_cases hcond : 3 ∣ rank + 1 ∧ 3 ∣ 2 ^ n + 1
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hcond.1, hcond.2⟩)))
    · have hgen : GGKacGenericCl ⟨.twA, rank, n⟩ 3 :=
        ⟨Nat.prime_three, by norm_num, h3, Or.inr (Or.inl rfl),
          (by intro h; cases h.1),
          (by intro h; exact hcond h.2)⟩
      rcases ggKacGenericCl_lanes hlab hgen with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
  ·
    have hgen : GGKacGenericCl ⟨.B, rank, n⟩ 3 :=
      ⟨Nat.prime_three, by norm_num, h3, Or.inr (Or.inr (Or.inl rfl)),
        (by intro h; cases h.1),
        (by intro h; cases h.1)⟩
    rcases ggKacGenericCl_lanes hlab hgen with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
  ·
    have hgen : GGKacGenericCl ⟨.C, rank, n⟩ 3 :=
      ⟨Nat.prime_three, by norm_num, h3, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
        (by intro h; cases h.1),
        (by intro h; cases h.1)⟩
    rcases ggKacGenericCl_lanes hlab hgen with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
  ·
    have hgen : GGKacGenericCl ⟨.D, rank, n⟩ 3 :=
      ⟨Nat.prime_three, by norm_num, h3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        (by intro h; cases h.1),
        (by intro h; cases h.1)⟩
    rcases ggKacGenericCl_lanes hlab hgen with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
  ·
    have hgen : GGKacGenericCl ⟨.twD, rank, n⟩ 3 :=
      ⟨Nat.prime_three, by norm_num, h3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
        (by intro h; cases h.1),
        (by intro h; cases h.1)⟩
    rcases ggKacGenericCl_lanes hlab hgen with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr h))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl rfl))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl rfl)))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr rfl)))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl rfl)))))))))

end CFSG.StandardType

end
