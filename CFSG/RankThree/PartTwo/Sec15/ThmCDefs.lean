module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

@[expose] def TwoMultLeTwo (S : Type) [Group S] : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E →
    Nonempty (E ⧸ Subgroup.center E ≃* S) →
    ∀ Z : Subgroup E, Z ≤ Subgroup.center E → IsPGroup 2 ↥Z → Nat.card ↥Z ≤ 2

@[expose] def KFactM2 : Prop :=
  TwoMultLeTwo CFSG.Blueprint.NativeSporadic.ON ∧
  TwoMultLeTwo ↥(alternatingGroup (Fin 7)) ∧
  (∃ _ : Fact (Nat.Prime 7),
    TwoMultLeTwo (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∧
  TwoMultLeTwo ↥(alternatingGroup (Fin 10)) ∧
  ∀ (m : ℕ), 3 ≤ m → ∀ (S : Type) [Group S], Sec4.IsoLThreePi S 2 m → TwoMultLeTwo S

end CFSG.RankThree.PartTwo.Sec15.ThmC
