module

public import CFSG.Permutation.FiveTransitive.Degree79ThreeFreeFromSeven
public import CFSG.Permutation.FiveTransitive.Degree79FiveFree
public import CFSG.Permutation.FiveTransitive.Degree79LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree79PureTwo
open MulAction

private theorem prime_eq_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (p : ℕ) (hp : p.Prime) (hd : p ∣ Nat.card (fixingSubgroup P s)) : p = 2 := by
  have hlt : p < 11 := by
    by_contra hn
    exact Degree79LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hd
  have h3 : p ≠ 3 := by
    intro he; subst p
    exact Degree79ThreeFreeFromSeven.not_dvd_five_fixer P hcard h5 hnotAlt
      (fun t ht => Degree79SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt t ht) s hs hd
  have h5p : p ≠ 5 := by
    intro he; subst p
    exact Degree79FiveFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
  have h7 : p ≠ 7 := by
    intro he; subst p
    exact Degree79SevenFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs hd
  interval_cases p <;> norm_num at *

private theorem card_eq_two_pow
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 2 ^ (Nat.card (fixingSubgroup P s)).factorization 2 := by
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' (by positivity)
  intro p
  rw [Nat.factorization_pow]
  by_cases h2 : p = 2
  · subst p
    simp [Nat.prime_two.factorization]
  have hz : (Nat.card (fixingSubgroup P s)).factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => h2 (prime_eq_two P hcard h5 hnotAlt s hs p hp hd)))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,h2]

theorem card_exponent
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hbound : ∀ S : Sylow 2 (fixingSubgroup P s), Nat.card S ≤ 2 ^ 22) :
    ∃ a : ℕ, a ≤ 22 ∧ Nat.card (fixingSubgroup P s) = 2 ^ a ∧
      Nat.card P = 2704501800 * 2 ^ a := by
  classical
  let _ := h5
  let H := fixingSubgroup P s
  let S : Sylow 2 H := Sylow.nonempty.some
  have hb := hbound S
  rw [S.card_eq_multiplicity] at hb
  have ha : (Nat.card H).factorization 2 ≤ 22 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (by omega : 23 ≤ (Nat.card H).factorization 2)
    norm_num at hh hb
    omega
  have hH := card_eq_two_pow P hcard h5 hnotAlt s hs
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,hH] at hm
  exact ⟨(Nat.card H).factorization 2,ha,hH,hm.symm⟩

end FiveTransitive.Degree79PureTwo

end CFSG
