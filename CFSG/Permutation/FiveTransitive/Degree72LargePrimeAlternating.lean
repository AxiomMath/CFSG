module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree28Classification
public import CFSG.Permutation.FiveTransitive.PrimePredFour

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeAlternating

open MulAction SylowFixedActionCore

theorem alternating_image
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    [Fintype (sylowFixedPoints X P s S)] :
    alternatingGroup (sylowFixedPoints X P s S) ≤
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let J := (toPermHom N F).range
  obtain ⟨hlower,hupper,hN5⟩ := Degree72LargePrimeFixed.bounds_and_transitive
    p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at hlower
  change Nat.card F ≤ 36 at hupper
  have hmod := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq a b
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩
  by_cases h28 : Nat.card F = 28
  · exact Degree28Classification.alternatingGroup_le J
      (by rwa [← Nat.card_eq_fintype_card]) hJ5
  by_cases h33 : Nat.card F = 33
  · exact PrimePredFour.alternatingGroup_le_of_sub_four_prime F J
      (by rw [← Nat.card_eq_fintype_card,h33]; decide) hJ5
      (by rw [← Nat.card_eq_fintype_card,h33]; decide)
  by_cases h34 : Nat.card F = 34
  · exact PrimePredFour.alternatingGroup_le_of_sub_three_prime F J
      (by rw [← Nat.card_eq_fintype_card,h34]; decide) hJ5
      (by rw [← Nat.card_eq_fintype_card,h34]; decide)
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
  · rwa [← Nat.card_eq_fintype_card]
  · rw [← Nat.card_eq_fintype_card]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [← Nat.card_eq_fintype_card]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [← Nat.card_eq_fintype_card]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hJ5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
end FiveTransitive.Degree72LargePrimeAlternating

end CFSG
