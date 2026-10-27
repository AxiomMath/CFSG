module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def K_19_20_oddAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X),
    ((CFSG.Blueprint.LieModel X .PSL 3 2 1 ∧ IsNontrivialParabolic X Y) ∨
      (IsAlt X 7 ∧ Y.index = 35)) →
    ∀ α : MulAut X, Odd (orderOf α) → Y.map α.toMonoidHom = Y → α ^ 3 = 1

@[expose] def K_19_20_J0shape : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), Shape19_16_124 X Y →
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) ∈ ({3, 60, 360, 20160, 1451520} : Finset ℕ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
