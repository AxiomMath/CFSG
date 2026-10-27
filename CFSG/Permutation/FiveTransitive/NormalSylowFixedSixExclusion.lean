module

public import CFSG.Permutation.FiveTransitive.SylowFixedSixImageExclusion
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedOrderPairs
public import CFSG.Permutation.FiveTransitive.NormalFourEvenStabilizer

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedSixExclusion

open MulAction GenericSylowFixedAction

theorem sylow_ne_bot
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    (S : Subgroup (fixingSubgroup N s)) ≠ ⊥ := by
  obtain ⟨g, hg, hgfix⟩ := NormalFourEvenStabilizer.exists_order_two_fixing_in_normal
    X P hcard h5 hnotAlt N s hs
  let u : fixingSubgroup N s := ⟨g, (mem_fixingSubgroup_iff N).mpr hgfix⟩
  have hu : orderOf u = 2 := (Subgroup.orderOf_coe u).symm.trans hg
  have hdvd : 2 ∣ Nat.card (fixingSubgroup N s) := by
    simpa only [hu] using orderOf_dvd_natCard u
  intro hS
  have hnot := S.not_dvd_index
  rw [hS, Subgroup.index_bot] at hnot
  exact hnot hdvd

private theorem fixed_degree_ne_six
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    Nat.card (sylowFixedPoints N X s S) ≠ 6 := by
  have hN4 := MinimalNormalFour.four_of_normal_of_not_alternating
    X P (by omega) h5 hnotAlt N
  intro hfix
  have hcases := NormalSylowFixedOrderPairs.degree_order_pairs P X h5 N hN4 s hs S
  have himage : Nat.card (MulAction.toPermHom (sylowNormalizer N X s S)
      (sylowFixedPoints N X s S)).range = 360 := by
    rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
    · omega
    · omega
    · exact h
    · omega
  exact SylowFixedSixImageExclusion.not_six_of_internal_card N X hN4 s hs S
    (sylow_ne_bot X P hcard h5 hnotAlt N s hs S) hfix himage

theorem degree_order_pairs
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    let F := sylowFixedPoints N X s S
    let L := (MulAction.toPermHom (sylowNormalizer N X s S) F).range
    (Nat.card F = 4 ∧ Nat.card L = 24) ∨
      (Nat.card F = 5 ∧ Nat.card L = 120) ∨
      (Nat.card F = 7 ∧ Nat.card L = 2520) := by
  have hN4 := MinimalNormalFour.four_of_normal_of_not_alternating
    X P (by omega) h5 hnotAlt N
  have hne := fixed_degree_ne_six X P hcard h5 hnotAlt N s hs S
  rcases NormalSylowFixedOrderPairs.degree_order_pairs P X h5 N hN4 s hs S with
    h4 | h5 | h6 | h7
  · exact Or.inl h4
  · exact Or.inr (Or.inl h5)
  · exact (hne h6.1).elim
  · exact Or.inr (Or.inr h7)

end FiveTransitive.NormalSylowFixedSixExclusion

end CFSG
