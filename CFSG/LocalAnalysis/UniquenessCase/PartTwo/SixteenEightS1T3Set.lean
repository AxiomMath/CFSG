module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Def

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

structure ThreeNat (A L T : Subgroup (MulAut W)) : Prop where
  elem : ∀ w : W, w * w = 1
  le : L ≤ A
  normal : A ≤ Subgroup.normalizer (L : Set (MulAut W))
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T A
  quasi : CFSG.Open.IsQuasisimple ↥L
  comm : commSub ⊤ L = ⊤
  sum : SumOfNatShape L ⊤ (fixV L) 3
  trans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
    ∃ g ∈ A ⊓ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom
  faithful : ∀ a ∈ A, (∀ w : W, a w * w⁻¹ ∈ fixV L) → a = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
