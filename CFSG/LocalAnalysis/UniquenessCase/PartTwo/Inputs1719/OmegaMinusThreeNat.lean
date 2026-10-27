module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

@[expose] def K_O4m4_ThreeNat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X Y : Subgroup (MulAut W), X ≤ Y → Y ≤ normalizer (X : Set (MulAut W)) →
      IsOmegaMinus ↥X 4 2 → SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 2) X ⊤ ⊥ 3 →
        CFSG.Open.pRank 17 (⊤ : Subgroup ↥Y) ≤ 1

@[expose] def K_O6m4_ThreeNatM : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X Y : Subgroup (MulAut W), X ≤ Y → Y ≤ normalizer (X : Set (MulAut W)) →
      IsOmegaMinus ↥X 6 2 → SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 2) X ⊤ ⊥ 3 →
        6 ≤ CFSG.Quasithin.E3.mParam Y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
