module

public import CFSG.Quasithin.MS93.S33Stmt
public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S33X52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
    S5.IsSp4Data M T L 1 F a → ⁅Xq M, L⁆ ≤ Uq M T L →
    ∀ (α' : Vtx (puAmalgam h.le)) (Y : Subgroup (puAmalgam h.le).Universal), S33Hyp h α' Y →
      Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) →
      (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 →
      Xq M = Uq M T L ⊔ Zq M L

end CFSG.Quasithin.MS93.S33
