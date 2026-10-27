module

public import CFSG.Quasithin.Background.E3AParamLeTwoClosure
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def K_U34AutE8 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    CFSG.Open.IsQuasisimple ↥(genFittingFStar Y) →
    LieModel (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) .PSU 3 2 2 →
    ∀ A : Subgroup Y, (∀ a ∈ A, a ^ 2 = 1) → 8 ≤ Nat.card A →
      Nat.card A = 8 ∧
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set Y)) = ⊤ ∧
      ∃ a ∈ A, a ≠ 1 ∧ 3 ∣ Nat.card ↥(Subgroup.normalClosure (A : Set Y) ⊓
        Subgroup.centralizer ({a} : Set Y))

theorem aParam_le_two_of_U34 (hK : K_U34AutE8) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (Y : Subgroup (MulAut W))
    (hq : CFSG.Open.IsQuasisimple ↥(genFittingFStar ↥Y))
    (hU : LieModel (↥(genFittingFStar ↥Y) ⧸ Subgroup.center ↥(genFittingFStar ↥Y))
      .PSU 3 2 2) :
    E3.aParam Y ≤ 2 :=
  CFSG.Quasithin.E3.aParam_le_two_of_E8GenClosure hW Y (hK ↥Y hq hU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
