module

public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def KS18OuterInvolution : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X : Subgroup Y) (t : Y) (E : Subgroup Y),
    CFSG.pCore 2 Y = ⊥ → X.Normal → Sec4.IsZ3L34OrHeisSL34 X → t ∉ X →
    X ⊔ Subgroup.zpowers t = ⊤ → IsPGroup 2 (Subgroup.zpowers t) →
    E ≤ X → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    E ≤ Subgroup.centralizer ({t} : Set Y) →
    (∀ B : Subgroup Y, B ≤ E → Nat.card B = 9 →
      ¬ perfectResidual Y ≤ Subgroup.centralizer (B : Set Y)) →
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t

end CFSG.RankThree.PartTwo.KFacts
