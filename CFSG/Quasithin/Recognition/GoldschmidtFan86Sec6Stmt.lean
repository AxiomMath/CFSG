module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan61 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (α : V) (z : G), z ∈ Cinv G α → valence Γ α ≠ 3

@[expose] def Fan62 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ T : Track Γ G, InXi T → ∀ z : G, z ∈ T.line.ZZ → z ≠ 1 →
    T.line.CoreSat z fun a b tL tR => b - a = 2 ∧ tR - b = 3 ∧ a - tL = 3

@[expose] def Fan63 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (α : V) (z : G), z ∈ Cinv G α → ∀ g : G, g * z * g⁻¹ ∈ ballStab Γ G 4 (g • α)

@[expose] def Fan64 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (α : V) (z : G), z ∈ Cinv G α →
    (∀ u ∈ Subgroup.closure (zBall Γ α z 2), ∀ v ∈ Subgroup.closure (zBall Γ α z 2),
      u * v = v * u) ∧ valence Γ α = 5 ∧
    ∀ x ∈ MulAction.stabilizer G α, orderOf x = valence Γ α →
      (Subgroup.centralizer ({x} : Set G)).relIndex (Subgroup.closure (zBall Γ α z 2)) = 2 ^ 4

end CFSG.Quasithin.Fan86
