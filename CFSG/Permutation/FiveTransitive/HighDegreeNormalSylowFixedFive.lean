module

public import CFSG.Permutation.FiveTransitive.NormalSylowFixedDegreeFive
public import CFSG.Permutation.FiveTransitive.MinimalNormalFour
public import CFSG.Permutation.FiveTransitive.OneFixerSuccessorTransitivity

public section

namespace CFSG

namespace FiveTransitive.HighDegreeNormalSylowFixedFive

open MulAction SubMulAction GenericSylowFixedAction

theorem five_transitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (N : Subgroup P) [N.Normal] [Nontrivial N]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s))
    (hF : Nat.card (sylowFixedPoints N X s S) = 5) :
    IsMultiplyPretransitive N X 5 := by
  classical
  have hN4 := MinimalNormalFour.four_of_normal_of_not_alternating
    X P (by omega) h5 hnotAlt N
  have hfix := NormalSylowFixedDegreeFive.fixing_pretransitive P X h5 N s hs S hF
  have hcardS : Nat.card s = 4 := by rwa [Nat.card_coe_set_eq]
  let E : s ≃ Fin 4 := Finite.equivFinOfCardEq hcardS
  let e : Fin 4 ↪ X := E.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have he : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (E.symm i).property
    · intro hx
      exact ⟨E ⟨x, hx⟩, congrArg Subtype.val (E.symm_apply_apply ⟨x, hx⟩)⟩
  apply OneFixerSuccessorTransitivity.succ_of_one_transitive_fixing N X 4 hN4 e
  rw [he]
  exact hfix

end FiveTransitive.HighDegreeNormalSylowFixedFive

end CFSG
