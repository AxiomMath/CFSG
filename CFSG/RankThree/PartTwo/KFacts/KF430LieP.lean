module

public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

@[expose] def KF430LieP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (L : Type) [Group L] [Finite L],
    (ChevalleyExceptionalModel L .G2 p 1 ∨ Nonempty (L ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (L ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (L ≃* projSL 4 (GaloisField p 1)))) →
    (∀ σ : MulAut L, orderOf σ = 3 → σ ∈ (MulAut.conj : L →* MulAut L).range) ∧
    Subgroup.center L = ⊥ ∧
    ∀ V : Subgroup L, CFSG.Assembly.IsElemAbelian 3 V → Nat.card V = 9 →
      ∃ n ∈ Subgroup.normalizer (V : Set L),
        (∃ x ∈ V, n ^ 2 * x * (n ^ 2)⁻¹ ≠ x) ∧ (∃ x ∈ V, n ^ 3 * x * (n ^ 3)⁻¹ ≠ x)

end CFSG.RankThree.PartTwo.KFacts
