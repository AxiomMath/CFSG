module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def ListCentralizerInvolutionsStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ListGroup S → ∀ T : Subgroup S, 4 ≤ Nat.card T →
    CorBHyp T → ∀ x ∈ Subgroup.centralizer (T : Set S), x * x = 1 → x ∈ T

@[expose] def ListOutElemAbelianBoundStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ListGroup S →
    ∀ A : Subgroup (Outer S), IsElemAbelian 2 A → Nat.card A ≤ 4

end CFSG.RankThree.GF2n.Stroth80
