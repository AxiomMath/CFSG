module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69Corollaries

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6

variable {G : Type} [Group G] [Finite G]

theorem X_le_center_sup_of_R6_9
    {D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G}
    (h69 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_9 D)
    (hsub : D.sig ⊆ D.sig1)
    {E : Subgroup G} (hE : E ≤ D.M) (hEel : CFSG.Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M)
    {X W : Subgroup G} (hX : X ≤ D.M) (hXcard : Nat.card X = 3)
    (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hnotN : ¬ Subgroup.normalizer (X : Set G) ≤ D.M)
    (hWle : W ≤ D.M) (hW3 : IsPGroup 3 W) (hXW : X ≤ W)
    (hXZ2 : X ≤ (Subgroup.upperCentralSeries ↥W 2).map W.subtype) :
    X ≤ (Subgroup.center ↥W).map W.subtype :=
  le_center_of_le_upperCentral_two_of_R6_9 (r := 3) (p := 3) h69 hsub
    Nat.prime_three (by decide) hE hEel hEcard hΓ Nat.prime_three hX hXcard hEX hnotN
    hWle hW3 hXW hXZ2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
