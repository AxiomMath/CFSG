module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

@[expose] def CoreSat (ℓ : Line Γ) (z : G) (P : ℤ → ℤ → ℤ → ℤ → Prop) : Prop :=
  (∃ a b tL tR, ℓ.IsCoreFix z a b tL tR) ∧ ∀ a b tL tR, ℓ.IsCoreFix z a b tL tR → P a b tL tR

end Line

@[expose] def zBall (Γ : SimpleGraph V) (α : V) (z : G) (k : ℕ) : Set G :=
  {w | ∃ g : G, Γ.dist α (g • α) ≤ k ∧ w = g * z * g⁻¹}

@[expose] def Fan59 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G), z ∈ T.line.ZZ → z ≠ 1 → ∀ a b tL tR : ℤ,
    T.line.IsCoreFix z a b tL tR → Even (tR - tL) → b - a = 2

@[expose] def Fan510 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ T : Track Γ G, XiI 1 T → ∀ z : G, z ∈ T.line.ZZ → z ≠ 1 →
    T.line.CoreSat z fun a b tL tR => b - a = 2 ∧ tR - b = a - tL ∧ tR - b ≤ 3

@[expose] def Fan511 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (j : ℕ) (T : Track Γ G), j ≠ 1 → XiI j T → ∀ z : G, z ∈ T.line.ZZ → z ≠ 1 →
    T.line.CoreSat z fun a b tL tR => b - a = 2 ∧ tR - b = a - tL

@[expose] def Fan519 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ T : Track Γ G, InXi T → ∀ z : G, z ∈ T.line.ZZ → z ≠ 1 →
    T.line.CoreSat z fun a b tL tR => b - a = 2 ∧ tR - b = a - tL ∧ tR - b ≤ 3

@[expose] def Fan512cen (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCore z a (a + 2) → z ∈ Cinv G (T.line.vert (a + 1))

@[expose] def Fan512a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCore z a (a + 2) → ∀ β : V, ¬ Equiv3 G (T.line.vert (a + 1)) β → Cinv G β = ∅

@[expose] def Fan512b (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCore z a (a + 2) →
    z ∈ ballStab Γ G 2 (T.line.vert (a + 1)) ∧
    ∀ (β : V) (l : List V) (h : V → G), ¬ Equiv3 G (T.line.vert (a + 1)) β → l.Nodup →
      (∀ u, u ∈ l ↔ Γ.Adj β u) → (∀ u, Γ.Adj β u → h u • T.line.vert (a + 1) = u) →
      (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
        (l.map fun u => h u * z * (h u)⁻¹).prod = 1

@[expose] def Fan512c (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ T : Track Γ G, InXi T → ∀ z : G, z ∈ T.line.ZZ → z ≠ 1 → ∀ a b tL tR : ℤ,
    T.line.IsCoreFix z a b tL tR → Even (tR - b) → tR - b = 2

@[expose] def Fan512d (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a : ℤ), InXi T → z ∈ T.line.ZZ → z ≠ 1 →
    T.line.IsCore z a (a + 2) → ∀ (g : G) (α' : V), g • T.line.vert (a + 1) = α' →
      Cinv G α' = {g * z * g⁻¹}

@[expose] def Fan513a (F : FanTree Γ G) : Prop :=
  Fan40 F → (∀ T : Track Γ G, ¬ Xi 1 T) → ∀ (n i : ℕ) (P : Arc Γ (2 * n)), 1 ≤ i → i + 1 ≤ 2 * n →
    ¬ RightSingular Γ G P.vert 0 i →
    (i + 1 < 2 * n → ¬ LeftSingular Γ G P.vert (i + 1) (2 * n)) →
    ∀ z₀ ∈ Cinv G (P.vert 0), ∀ z₁ ∈ Cinv G (P.vert (2 * n)), z₀ ≠ z₁

@[expose] def Fan513b (F : FanTree Γ G) : Prop :=
  Fan40 F → (∀ T : Track Γ G, ¬ Xi 1 T) → ∀ T : Track Γ G, InXi T → ∀ a d : ℤ, d.natAbs ≤ 4 →
    ∀ x ∈ MulAction.stabilizer G (T.line.vert (a + d)),
      x ∉ MulAction.stabilizer G (T.line.vert a) →
      ∀ z ∈ Cinv G (T.line.vert a), x * z ≠ z * x

@[expose] def Fan517a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (α : V) (z : G), valence Γ α ≠ 3 → z ∈ Cinv G α →
    Subgroup.closure (zBall Γ α z 2) ≤ nbrStab Γ G α ∧
      ∀ x ∈ Subgroup.closure (zBall Γ α z 2), ∀ y ∈ Subgroup.closure (zBall Γ α z 2),
        fcomm x y ∈ Subgroup.zpowers z

@[expose] def Fan517c (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (α : V) (z : G), valence Γ α ≠ 3 → z ∈ Cinv G α →
    ∀ g₁ g₂ g₃ : G, Γ.dist α (g₁ • α) = 2 → Γ.dist α (g₂ • α) = 2 → Γ.dist α (g₃ • α) = 2 →
      g₁ * z * g₁⁻¹ * (g₂ * z * g₂⁻¹) * (g₃ * z * g₃⁻¹) ∉ Subgroup.zpowers z

end CFSG.Quasithin.Fan86
