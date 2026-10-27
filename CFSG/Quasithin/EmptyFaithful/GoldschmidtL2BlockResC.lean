module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockType

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15120L2BlockResC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → L ∈ cComp (g1_1516 Z₁) → CharTwo L → ListA15120 L →
    IsBlock2 (L ⊔ s1516 T Z₁) L →
    (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∧ IsBorelOfBlock L (mZ1516 Mc Z₁ ⊓ L)

theorem input15120L2BlockResC_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h42 : AsB42)
    (hLJ : Input15120LJ) : Input15120L2BlockResC := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hLc hchar hA hblock
  exact ⟨input15120L2BlockType_holds h42 hLJ G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hA hblock,
    GoldMLA.isBorelOfBlock_of_cComp h37 h38 hc hLc hA⟩

end CFSG.Quasithin
