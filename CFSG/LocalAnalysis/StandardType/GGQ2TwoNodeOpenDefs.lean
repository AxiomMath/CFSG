module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2TwoNodeOpenInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      (((GGQ2S08RowTwA p 6 L J ∨ GGQ2S08RowTwA p 9 L J) ∧ x ∉ L) ∨
        ((GGQ2S08RowTwA p 6 K J ∨ GGQ2S08RowTwA p 9 K J ∨ ∃ N, N < 12 ∧ GGQ2S08RowA p N K J) ∧
          y ∉ K)) →
      ¬ ((GGQ2S08PosTwABig p L J ∧ x ∉ L) ∨ (GGQ2S08PosTwABig p K J ∧ y ∉ K) ∨
        (GGQ2S08PosABig p K J ∧ y ∉ K)) →
      ¬ GGQ2TNBigSel p Bs L x → ¬ GGQ2TNBigSel p Bs K y → ¬ GGQ2TN9Sel p B Bs x L D J →
        ¬ GGQ2TN9SelK p B Bs x L D J y K →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end CFSG.StandardType

end
