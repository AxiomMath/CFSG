module

public import CFSG.Permutation.FiveTransitive.NormalSylowFixedSevenExclusion
public import CFSG.Permutation.FiveTransitive.HighDegreeNormalSylowFixedFive

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedFourFive

open MulAction GenericSylowFixedAction

private theorem degree_order_pairs
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    let F := sylowFixedPoints N X s S
    let L := (toPermHom (sylowNormalizer N X s S) F).range
    (Nat.card F = 4 ∧ Nat.card L = 24) ∨ (Nat.card F = 5 ∧ Nat.card L = 120) := by
  have hseven := NormalSylowFixedSevenExclusion.fixed_degree_ne_seven
    X P hcard h5 hnotAlt N s hs S
  rcases NormalSylowFixedSixExclusion.degree_order_pairs X P hcard h5 hnotAlt N s hs S with
    h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hseven h.1).elim

theorem fixed_degree_eq_five_of_odd
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (hodd : Odd (Fintype.card X))
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    Nat.card (sylowFixedPoints N X s S) = 5 := by
  have hp := fixed_degree_modEq N X s S
  change Nat.card X % 2 = Nat.card (sylowFixedPoints N X s S) % 2 at hp
  have hone := Nat.odd_iff.mp hodd
  rw [Nat.card_eq_fintype_card, hone] at hp
  rcases degree_order_pairs X P hcard h5 hnotAlt N s hs S with h | h
  · omega
  · exact h.1

theorem five_transitive_of_odd
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (hodd : Odd (Fintype.card X)) : IsMultiplyPretransitive N X 5 := by
  classical
  let e : Fin 4 ↪ X := (Fin.castLEEmb (by omega : 4 ≤ Fintype.card X)).trans
    (Fintype.equivFin X).symm.toEmbedding
  let s := Set.range e
  have hs : s.ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective e.injective
  let S : Sylow 2 (fixingSubgroup N s) := Classical.arbitrary _
  exact HighDegreeNormalSylowFixedFive.five_transitive X P hcard h5 hnotAlt N s hs S
    (fixed_degree_eq_five_of_odd X P hcard h5 hnotAlt N hodd s hs S)

end FiveTransitive.NormalSylowFixedFourFive

end CFSG
