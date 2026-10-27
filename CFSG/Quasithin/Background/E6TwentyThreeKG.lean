module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

@[expose] def E623CentA5Block : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X : Subgroup Y) (u : Y),
    CFSG.IsQuasisimple ↥X →
    (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 2 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 3 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 2 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSp 2 2 2 ∨
      Nonempty (↥X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (↥X ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 7))) →
    u ∈ Subgroup.normalizer (X : Set Y) → u ^ 2 = 1 → u ∉ Subgroup.centralizer (X : Set Y) →
    ∀ B : Subgroup Y, IsBlock2 (X ⊓ Subgroup.centralizer ({u} : Set Y)) B → ¬ IsAltType B 5

end E6

end CFSG.Quasithin
