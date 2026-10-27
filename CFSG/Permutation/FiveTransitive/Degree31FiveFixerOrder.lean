module

public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerArithmetic
public import CFSG.Permutation.FiveTransitive.Degree31FiveFree
public import CFSG.Permutation.FiveTransitive.Degree31SevenFree
public import CFSG.Permutation.FiveTransitive.Degree31LargePrimeFree
public import CFSG.Permutation.FiveTransitive.Degree31SylowThreeEntrance

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveFixerOrder

open MulAction

private theorem prime_divisor
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card (fixingSubgroup P s)) : p = 2 ∨ p = 3 := by
  have hfive := Degree31FiveFree.five_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs
  have hseven := Degree31SevenFree.seven_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs
  by_cases hlarge : 11 ≤ p
  · exact (Degree31LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp hlarge hd).elim
  · have hle : p ≤ 10 := by omega
    have hcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p <;> norm_num at hp <;> norm_num
    rcases hcases with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hfive hd).elim
    · exact (hseven hd).elim

private theorem nine_not_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 9 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hd
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have h9 : 9 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at h9; norm_num at h9
  have hc := Degree31SylowThreeEntrance.card_eq_three P hcard h5 hnotAlt s hs S hS
  rw [hc] at h9
  norm_num at h9

theorem five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : Nat.card (fixingSubgroup P s) = 4096 :=
  Degree31FiveFixerArithmetic.five_fixer_card P hcard h5 hnotAlt s hs
    (prime_divisor P hcard h5 hnotAlt s hs) (nine_not_dvd P hcard h5 hnotAlt s hs)

end FiveTransitive.Degree31FiveFixerOrder

end CFSG
