module

public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S310a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → IsSp4Full M T L → critDist (puAmalgam h.le) = 4 →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
          (a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)),
        Fintype.card F = 2 ^ k → Function.Surjective a →
        IsSumOfNaturalModulesVia (stab _ (baseA _))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)) ⊓ S5.bSub h.le L (baseA _))
          a false 1 →
        ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
            ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ≤
          S5.dSub h.le L (baseA _) →
        ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)),
            S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2))⁆ =
          ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
            ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ∧
        Nat.card ↥⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)),
            S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2))⁆ ≤ 2 ^ k

@[expose] def S310m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → IsSp4Full M T L → critDist (puAmalgam h.le) = 4 →
    ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
          (a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)),
        Fintype.card F = 2 ^ k → Function.Surjective a →
        IsSumOfNaturalModulesVia (stab _ (baseA _))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)))
          (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)) ⊓ S5.bSub h.le L (baseA _))
          a false 1 →
        ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
            ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ≤
          S5.dSub h.le L (baseA _) →
        2 ^ k < (S5.bSub h.le L (baseA _)).relIndex (ZM _ (geo _ (baseA _) α' 2)) ∨
          2 ^ k < (S5.bSub h.le L (geo _ (baseA _) α' 2)).relIndex (ZM _ α') ∨
          ∀ g ∈ stab _ (geo _ (baseA _) α' 2), g • baseA (puAmalgam h.le) ≠ α'

end CFSG.Quasithin.MS93
