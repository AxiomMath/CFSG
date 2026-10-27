module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec15

open scoped MatrixGroups

@[expose] def KSL2pAutThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 < p →
    ∀ E : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))),
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≤ 3

@[expose] def KSL2pNotList148 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 < p →
    IsEmpty (PSL(2, ZMod p) ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
    IsEmpty (PSL(2, ZMod p) ≃* alternatingGroup (Fin 5)) ∧
    IsEmpty (PSL(2, ZMod p) ≃* alternatingGroup (Fin 7)) ∧
    IsEmpty (PSL(2, ZMod p) ≃* alternatingGroup (Fin 10)) ∧
    (∀ _ : Fact (Nat.Prime 7), IsEmpty (PSL(2, ZMod p) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) ∧
    ∀ n : ℕ, 1 ≤ n → ¬ Sec4.IsoLThreePi PSL(2, ZMod p) 2 (3 * n)

end CFSG.RankThree.PartTwo.Sec15
