module

public import CFSG.Quasithin.EmptyFaithful.S146zYFOInst
public import CFSG.Quasithin.EmptyFaithful.S146zYFOFive

public section

namespace CFSG.Quasithin.S146zY

namespace FiveOdd

theorem mod_five_ne_zero_of_prime {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) : p % 5 ≠ 0 := fun h =>
  hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 (Nat.dvd_of_mod_eq_zero h)).symm

end FiveOdd

open CFSG.Assembly.LowTwoRank FiveOdd

theorem facts134Five_psl3Odd_of_plus
    (hP : ∀ p : ℕ, p.Prime → p % 5 = 1 →
      NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 →
      NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1 := by
  intro p hp _ hp5
  have hmod : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have := mod_five_ne_zero_of_prime hp hp5
    omega
  rcases hmod with h | h | h | h
  · exact hP p hp h
  · exact noE25Config_of_not_dvd fun X _ hX h25 =>
      not_five_dvd_card_of_statedPSL_three (Or.inl h) hX ((by norm_num : 5 ∣ 25).trans h25)
  · exact noE25Config_of_not_dvd fun X _ hX h25 =>
      not_five_dvd_card_of_statedPSL_three (Or.inr h) hX ((by norm_num : 5 ∣ 25).trans h25)
  · exact noE25Config_of_noElem fun X _ hX => noElemTwentyFive_of_statedPSL_three h hX

theorem facts134Five_psu3Odd_of_minus
    (hM : ∀ p : ℕ, p.Prime → p % 5 = 4 →
      NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1)
    (hF : NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 5 1) :
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1 := by
  intro p hp _
  have hmod : p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  rcases hmod with h | h | h | h | h
  · have : p = 5 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1
      (Nat.dvd_of_mod_eq_zero h)).symm
    subst this
    exact hF
  · exact noE25Config_of_noElem fun X _ hX => noElemTwentyFive_of_statedPSU_three h hX
  · exact noE25Config_of_not_dvd fun X _ hX h25 =>
      not_five_dvd_card_of_statedPSU_three (Or.inl h) hX ((by norm_num : 5 ∣ 25).trans h25)
  · exact noE25Config_of_not_dvd fun X _ hX h25 =>
      not_five_dvd_card_of_statedPSU_three (Or.inr h) hX ((by norm_num : 5 ∣ 25).trans h25)
  · exact hM p hp h

theorem facts134Five_psl3Odd : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1 :=
  facts134Five_psl3Odd_of_plus facts134Five_psl3Plus

theorem facts134Five_psu3Odd : ∀ p : ℕ, p.Prime → p ≠ 2 →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1 :=
  facts134Five_psu3Odd_of_minus facts134Five_psu3Minus facts134Five_psu3Five

end CFSG.Quasithin.S146zY
