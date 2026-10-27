module

public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

@[expose] def SeitzL3Pi : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi X p e → p ^ e ≠ 2 → p ^ e ≠ 4 →
    ∀ F : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 →
      Subgroup.closure {x : X | ∃ φ ∈ F, φ ≠ 1 ∧ φ x = x} = ⊤

end CFSG.RankThree.PartTwo.Sec19
