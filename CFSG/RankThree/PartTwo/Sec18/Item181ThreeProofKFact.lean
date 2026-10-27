module

public import CFSG.RankThree.PartTwo.Sec3.ElemTwoModuleBound
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KS181GraphFieldModule : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X : Subgroup Y) (t : Y) (E : Subgroup Y),
    CFSG.pCore 2 Y = ⊥ → X.Normal → Sec4.IsZ3L34OrHeisSL34 X → t ∉ X →
    X ⊔ Subgroup.zpowers t = ⊤ → IsPGroup 2 (Subgroup.zpowers t) →
    E ≤ X → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    E ≤ Subgroup.centralizer ({t} : Set Y) →
    (∀ B : Subgroup Y, B ≤ E → Nat.card B = 9 →
      ¬ perfectResidual Y ≤ Subgroup.centralizer (B : Set Y)) →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ ρ : Y →* MulAut V, (∃ y ∈ perfectResidual Y, ρ y ≠ 1) →
      4 ≤ Nat.card (Sec3.commHom (ρ t)).range ∧
      (Nonempty (perfectResidual Y ≃* projSL 3 (GaloisField 2 2)) →
        16 ≤ Nat.card (Sec3.commHom (ρ t)).range)

end CFSG.RankThree.PartTwo.KFacts
