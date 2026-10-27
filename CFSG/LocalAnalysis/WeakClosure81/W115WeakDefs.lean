module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

@[expose] def W4Lem11_5Weak : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor ↥L .M22 →
      IsIrrOn L ⊤ ⊥ →
        8 ≤ E3.mParam Y ∨ rk W = 10

@[expose] def W4Lem11_6Weak : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L → IsQuasisimple ↥L → O2Trivial L →
      Nat.card (Subgroup.center ↥L) = 3 → IsSpor (↥L ⧸ Subgroup.center ↥L) .M22 →
      IsIrrOn L ⊤ ⊥ →
        4 ≤ E3.mParam Y

end CFSG.LocalAnalysis.WeakClosure81
