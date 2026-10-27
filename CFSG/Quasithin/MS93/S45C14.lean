module

public import CFSG.Quasithin.MS93.S45Loc
public import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

@[expose] def Ctx.HC14 {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ) :
    Prop :=
  ∀ (p : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N →
    ∀ a : ℕ, Even a → 34 ≤ a → a + 30 ≤ N →
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
        Hloc c.hyp.le L (p a) ∧
      ¬ frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
        Uloc c.hyp.le L (p a) ⊔ Hloc c.hyp.le L (p a)

end CFSG.Quasithin.MS93.S45
