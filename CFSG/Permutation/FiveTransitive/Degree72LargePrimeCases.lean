module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeAlternating

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeCases
open MulAction SylowFixedActionCore

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    (p = 11 ∧ Nat.card (sylowFixedPoints X P s S) = 6) ∨
    (p = 13 ∧ Nat.card (sylowFixedPoints X P s S) = 7) ∨
    (p = 17 ∧ Nat.card (sylowFixedPoints X P s S) = 21) ∨
    (p = 19 ∧ Nat.card (sylowFixedPoints X P s S) = 15) ∨
    (p = 23 ∧ Nat.card (sylowFixedPoints X P s S) = 26) ∨
    (p = 29 ∧ Nat.card (sylowFixedPoints X P s S) = 14) ∨
    (p = 31 ∧ Nat.card (sylowFixedPoints X P s S) = 10) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hlo,hhi,_⟩ := Degree72LargePrimeFixed.bounds_and_transitive p hp P hcard h5 hnotAlt s hs S hS
  have hAlt := Degree72LargePrimeAlternating.alternating_image p hp hcases P hcard h5 hnotAlt s hs S hS
  have hb := (fixed_card_bound_of_alternating_normalizer_action X P s hs S hAlt).2
    (by rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  change Fintype.card F - 5 < p at hb
  rw [← Nat.card_eq_fintype_card] at hb
  dsimp only [F] at hm hb
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end FiveTransitive.Degree72LargePrimeCases

end CFSG
