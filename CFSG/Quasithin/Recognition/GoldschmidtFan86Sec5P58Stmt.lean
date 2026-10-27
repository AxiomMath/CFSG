module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan57bT (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ),
    z ∈ T.line.ZZ → z' ∈ T.line.ZZ → T.line.IsCoreFix z a b tL tR →
    T.line.IsCoreFix z' a' b' tL' tR' →
    T.line.InPerfectPos z z' a b tL tR a' b' tL' tR' → tR - b ≤ 2

@[expose] def Fan58aT (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ),
    z ∈ T.line.ZZ → z' ∈ T.line.ZZ → T.line.IsCoreFix z a b tL tR →
    T.line.IsCoreFix z' a' b' tL' tR' →
    T.line.InPos z z' a b tL tR a' b' tL' tR' → tR - b ≤ 2 → a' - tL' ≤ 2 →
    ((tR - b = 1 ∧ a' - tL' = 1) ∨ T.line.InPerfectPos z z' a b tL tR a' b' tL' tR') ∧
      ¬ ((tR - b = 1 ∧ a' - tL' = 1) ∧ T.line.InPerfectPos z z' a b tL tR a' b' tL' tR')

@[expose] def ZcFin (_ : FanTree Γ G) : Prop :=
  ∀ (T : Track Γ G) (u : G), u ∈ T.line.Zc → u ≠ 1 →
    ∃ tL tR : ℤ, ∀ j : ℤ, j ∈ T.line.fixIdx u ↔ tL ≤ j ∧ j ≤ tR

end CFSG.Quasithin.Fan86
