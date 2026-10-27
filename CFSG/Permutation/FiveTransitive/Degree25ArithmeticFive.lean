module

public import CFSG.Permutation.FiveTransitive.Degree25FiveGoursat
public import CFSG.Permutation.FiveTransitive.Degree25ArithmeticSeven

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem sylow_five_card_eq_five_of_dvd_not_square
    (G : Type) [Group G] [Fintype G]
    (hfive : 5 ∣ Nat.card G)
    (hnotFiveSq : ¬5 ^ 2 ∣ Nat.card G)
    (S : Sylow 5 G) :
    Nat.card S = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := hfive
  have hmPos : m ≠ 0 := by
    intro hmZero
    rw [hmZero, mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have hnotFive : ¬5 ∣ m := by
    intro hfiveM
    obtain ⟨k, hk⟩ := hfiveM
    apply hnotFiveSq
    refine ⟨k, ?_⟩
    rw [hm, hk]
    norm_num [pow_two]
    ring
  apply Degree24.sylow_card_eq_prime_of_card_eq_prime_mul
    G 5 m hmPos hnotFive
  exact hm

theorem five_point_stabilizer_card_cases_five_cubed
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    let h := Nat.card (fixingSubgroup P s)
    h = 12000 ∨ h = 1944000 ∨ h = 288000 ∨
      h = 46656000 ∨ h = 1024000 ∨
      h = 165888000 := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change
    h = 12000 ∨ h = 1944000 ∨ h = 288000 ∨
      h = 46656000 ∨ h = 1024000 ∨
      h = 165888000
  have hcases :
      h = 270 ∨ h = 6480 ∨ h = 12000 ∨ h = 960 ∨
      h = 1944000 ∨ h = 288000 ∨ h = 23040 ∨
      h = 46656000 ∨ h = 552960 ∨ h = 1024000 ∨
      h = 81920 ∨ h = 165888000 := by
    simpa only [H, h] using
      five_point_stabilizer_card_cases_without_seven
        X P hcard h5 hnotAlt s hs
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 H := Sylow.nonempty.some
  have heliminate
      (hfive : 5 ∣ h)
      (hnotFiveSq : ¬5 ^ 2 ∣ h) :
      False := by
    have hScard : Nat.card S = 5 :=
      sylow_five_card_eq_five_of_dvd_not_square
        H
        (by simpa only [h] using hfive)
        (by simpa only [h] using hnotFiveSq)
        S
    exact hnotAlt
      (alternatingGroup_le_of_sylow_five_card_five
        X P hcard h5 hnotAlt s hs S hScard)
  rcases hcases with
    hcase | hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase | hcase | hcase | hcase
  · exact False.elim
      (heliminate
        (by norm_num [hcase])
        (by norm_num [hcase]))
  · exact False.elim
      (heliminate
        (by norm_num [hcase])
        (by norm_num [hcase]))
  · norm_num [hcase]
  · exact False.elim
      (heliminate
        (by norm_num [hcase])
        (by norm_num [hcase]))
  · norm_num [hcase]
  · norm_num [hcase]
  · exact False.elim
      (heliminate
        (by norm_num [hcase])
        (by norm_num [hcase]))
  · norm_num [hcase]
  · exact False.elim
      (heliminate
        (by norm_num [hcase])
        (by norm_num [hcase]))
  · norm_num [hcase]
  · exact False.elim
      (heliminate
        (by norm_num [hcase])
        (by norm_num [hcase]))
  · norm_num [hcase]

end FiveTransitive.Degree25

end CFSG
