module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan514 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a tL tR : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCoreFix z a (a + 2) tL tR → valence Γ (T.line.vert (a + 1)) = 3 → tR - (a + 2) ≤ 2

@[expose] def Fan515a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a tL tR : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCoreFix z a (a + 2) tL tR → valence Γ (T.line.vert (a + 1)) ≠ 3 →
    5 ≤ tR - (a + 2) → ∀ k j : ℤ, 0 ≤ j → 2 * j + 3 ≤ tR - (a + 2) →
      T.τ ^ (k + j) * z * T.τ ^ (-(k + j)) ∈ ballStab Γ G 2 (T.line.vert (a + 1 + 2 * k)) ∧
      T.τ ^ (k - j) * z * T.τ ^ (-(k - j)) ∈ ballStab Γ G 2 (T.line.vert (a + 1 + 2 * k))

@[expose] def Fan515b (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z z' : G) (a tL tR a' b' tL' tR' : ℤ), InXi T → z ∈ T.line.ZZ →
    z ≠ 1 → T.line.IsCoreFix z a (a + 2) tL tR → z' ∈ T.line.ZZ →
    T.line.InPos z z' a (a + 2) tL tR a' b' tL' tR' →
    valence Γ (T.line.vert (a + 1)) ≠ 3 → 5 ≤ tR - (a + 2) →
    ∀ k : ℕ, 3 ≤ k →
      (∀ g : G, g * fcomm z z' = fcomm z z' * g →
        g ∈ MulAction.stabilizer G (T.line.vert (a + 1 + k)) →
          g ∈ MulAction.stabilizer G (T.line.vert (a + 1 + k + 1))) →
      ¬ RightSingular Γ G (T.line.arc (a + 1) k).vert 0 k →
      ∀ g ∈ Arc.GcircL G (T.line.arc (a + 3) (k - 1)), g * fcomm z z' = fcomm z z' * g

@[expose] def Fan516 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a tL tR : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCoreFix z a (a + 2) tL tR → valence Γ (T.line.vert (a + 1)) ≠ 3 → tR - (a + 2) ≤ 5

@[expose] def Fan518 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a tL tR : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCoreFix z a (a + 2) tL tR → valence Γ (T.line.vert (a + 1)) ≠ 3 → tR - (a + 2) ≤ 3

end CFSG.Quasithin.Fan86
