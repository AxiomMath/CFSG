module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

@[expose] def W4Lem11_5Twelve : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor ↥L .M22 →
      IsIrrOn L ⊤ ⊥ →
        12 ≤ E3.mParam Y ∨ rk W = 10

end CFSG.LocalAnalysis.WeakClosure81
