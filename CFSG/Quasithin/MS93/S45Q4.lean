module

public import CFSG.Quasithin.MS93.S45Loc
public import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

@[expose] def Ctx.HQ4 {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ) :
    Prop :=
  ∀ (p : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N → ∀ a : ℕ, Even a →
    24 ≤ a → a + 24 ≤ N → ∀ g ∈ stab (puAmalgam c.hyp.le) (p a),
      ZM (puAmalgam c.hyp.le) (g • p (a + 4)) ≤ Qv _ (p (a + 4))

end CFSG.Quasithin.MS93.S45
