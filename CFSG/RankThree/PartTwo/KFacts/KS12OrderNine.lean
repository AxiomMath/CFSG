module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def KS12OrderNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (Sec4.IsSLThreePi X ∨ Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X Blueprint.NativeSporadic.M22) →
    ∀ v : X, orderOf v = 9 → v ^ 3 ∈ Subgroup.center X →
      (∃ w : X, orderOf w = 3 ∧ w ∉ Subgroup.center X ∧ w * v = v * w) ∧
        ∃ t : X, orderOf t = 2 ∧ t * v = v * t

end CFSG.RankThree.PartTwo.KFacts
