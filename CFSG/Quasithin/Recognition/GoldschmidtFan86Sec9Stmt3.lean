module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan910b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, S.Star → ∃ e₁ e₂ : Fin 2,
    S.wA 1 = S.yEta 3 * S.yEta 4 * S.zMu1 3 * S.zNb 2 ^ (e₁ : ℕ) * S.zNb 0 ^ (e₂ : ℕ)

@[expose] def Fan912 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, S.Star →
    P2Rel912 S.xβ S.t (S.w) (S.wA 1) S.ub S.zMu S.yMu S.zNb ∧
    (Nat.card ↥S.D.calpha = 4 → P2cRel912 S.ub S.c S.zMu S.yMu S.zNb) ∧
    (Nat.card ↥S.D.calpha = 2 → S.c = S.zNb 0)

end CFSG.Quasithin.Fan86
