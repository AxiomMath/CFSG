module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

@[expose] def K_SU3NaturalModuleTwo : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y K : Subgroup (MulAut W)),
      K ≤ Y → CFSG.Open.IsComponentOf K Y → K ≠ ⊥ → IsSU3 ↥K 2 →
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      IsBasicModule Y →
      fixV (⨆ X ∈ conjSet K Y, X) = ⊥ →
      E3.mParam Y < 2 * 2 + 2 →
      CNatModSU3Sub W (CFSG.Quasithin.commSub (⊤ : Subgroup W) K) K 2 ∧
        E3.mParam Y = 2 * 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
