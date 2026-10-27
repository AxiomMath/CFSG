module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15120L2BlockType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → ListA15120 L → IsBlock2 (L ⊔ s1516 T Z₁) L →
    IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n

end CFSG.Quasithin
