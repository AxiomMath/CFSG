module

public import CFSG.RankThree.PartOne.S12.InputsEleven

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FieldLmModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (c : G) (K : Subgroup G) (m : ℕ), (m = 3 ∨ m = 4) →
    CFSG.IsQuasisimple ↥K → ¬ 7 ∣ Nat.card (Subgroup.center ↥K) → InducesFieldAut 7 c K →
    StatedClassicalModel
      ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))) .PSL m 2 1 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 7 ∧
        Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin m) F)

end CFSG.RankThree.PartOne.MB3
