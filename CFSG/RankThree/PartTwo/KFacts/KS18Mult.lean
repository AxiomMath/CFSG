module

public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Sec13

@[expose] def KS18Mult : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Group.IsPerfect X →
    Z ≤ Subgroup.center X → Nat.Coprime 6 (Nat.card Z) →
    (IsLThreePi (X ⧸ Z) ∨ Nonempty (X ⧸ Z ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (X ⧸ Z ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (X ⧸ Z ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (X ⧸ Z ≃* CFSG.Blueprint.NativeSporadic.M22)) →
    Z = ⊥

end CFSG.RankThree.PartTwo.KFacts
