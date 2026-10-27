module

public import CFSG.Quasithin.MS93.S5BLamSel

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512Z

@[expose] def OneCF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le),
        S5B.IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂ →
        ∀ μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2),
          S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
            (((S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
              XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)

end S512Z

end CFSG.Quasithin.MS93
