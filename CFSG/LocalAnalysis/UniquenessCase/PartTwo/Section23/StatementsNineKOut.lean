module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KOut23 : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    ((∃ a : ℕ, IsL2 S a ∨ IsSz S a) ∨
      (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd S q) ∨ IsJ1 S) →
    ∀ P : Subgroup (MulAut S), Group.IsPerfect P →
      P ≤ (MulAut.conj : S →* MulAut S).range

end CFSG.LocalAnalysis.UniquenessCase.UC22
