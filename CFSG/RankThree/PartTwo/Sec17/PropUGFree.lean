module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec17

@[expose] def J2GenByTwoSubgroups : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ E : Subgroup X, Nat.card E = 9 →
      sSup {S : Subgroup X | IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set X)} = ⊤

@[expose] def J2CoverHasElemAbelianEight : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Z ≤ Subgroup.center X →
    IsPGroup 2 Z → Group.IsPerfect X → Nonempty ((X ⧸ Z) ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∃ E : Subgroup X, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8

end CFSG.RankThree.PartTwo.Sec17
