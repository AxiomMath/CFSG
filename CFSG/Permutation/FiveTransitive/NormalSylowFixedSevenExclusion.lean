module

public import CFSG.Permutation.FiveTransitive.NormalSylowFixedSevenTransitivity
public import CFSG.Permutation.FiveTransitive.SylowFixedSevenExclusion
public import CFSG.Permutation.FiveTransitive.NormalSylowFixedSixExclusion
public import CFSG.Permutation.FiveTransitive.OneFixerSuccessorTransitivity

public section

namespace CFSG

namespace FiveTransitive.NormalSylowFixedSevenExclusion

open MulAction GenericSylowFixedAction FixedSetNormalizerPerm

private theorem even_fixed
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s))
    (hseven : Nat.card (sylowFixedPoints N X s S) = 7) :
    EvenSixTupleLocal.EvenFixed N X (sylowImage N X s S) := by
  classical
  let F := sylowFixedPoints N X s S
  let A := sylowNormalizer N X s S
  let Q := sylowImage N X s S
  let _ := Fintype.ofFinite F
  let _ := Classical.decEq F
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ := Classical.decEq (fixedPoints Q X)
  let e : fixedPoints Q X ≃ F :=
    (Set.equivOfEq (SylowFixedSixImageExclusion.internal_fixed_eq N X s S)).symm
  intro n hn
  have hp : e.permCongr (fixedPerm N X Q n hn) = toPermHom A F ⟨n,hn⟩ := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  have hmem : toPermHom A F ⟨n,hn⟩ ∈ alternatingGroup F := by
    rw [← FixedSevenInternalAction.image_eq_alternating G X h5 N hN4 s hs S hseven]
    exact ⟨⟨n,hn⟩,rfl⟩
  rw [← Equiv.Perm.sign_permCongr e, hp]
  exact Equiv.Perm.mem_alternatingGroup.mp hmem

private theorem fixed_degree_ne_seven_of_nontrivial
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s))
    (hS : (S : Subgroup (fixingSubgroup N s)) ≠ ⊥) :
    Nat.card (sylowFixedPoints N X s S) ≠ 7 := by
  intro hseven
  have hfix := NormalSylowFixedSevenTransitivity.fixing_pretransitive
    G X h5 N hN4 s hs S hseven
  obtain ⟨e,he⟩ := BaseSylowConjugacy.exists_embedding_range X 4 s hs
  have hN5 : IsMultiplyPretransitive N X 5 := by
    apply OneFixerSuccessorTransitivity.succ_of_one_transitive_fixing N X 4 hN4 e
    rw [he]
    exact hfix
  exact SylowFixedSevenExclusion.not_seven_of_even_fixed N X hN5 s hs S hS hseven
    (even_fixed G X h5 N hN4 s hs S hseven)

theorem fixed_degree_ne_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s)) :
    Nat.card (sylowFixedPoints N X s S) ≠ 7 := by
  have hN4 := MinimalNormalFour.four_of_normal_of_not_alternating
    X P (by omega) h5 hnotAlt N
  exact fixed_degree_ne_seven_of_nontrivial P X h5 N hN4 s hs S
    (NormalSylowFixedSixExclusion.sylow_ne_bot X P hcard h5 hnotAlt N s hs S)

end FiveTransitive.NormalSylowFixedSevenExclusion

end CFSG
