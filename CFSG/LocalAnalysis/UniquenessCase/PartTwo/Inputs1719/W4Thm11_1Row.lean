module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def W4Thm11_1Row (s : TauCeti.SporadicName) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → Fstar Y = L →
      IsQuasisimple ↥L → O2Trivial L → IsSpor (↥L ⧸ Subgroup.center ↥L) s →
        E3.aParam Y ≤ tableA s ∧ tableM s ≤ E3.mParam Y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
