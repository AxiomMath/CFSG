module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArc
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ZLab

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin CFSG.Open

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan65 (_ : FanTree Γ G) : Prop :=
  (∀ α : V, valence Γ α = 5 → ∀ x ∈ MulAction.stabilizer G α, orderOf x = 5 →
    (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G α) = 2 ^ 8) ∧
  ∀ α : V, valence Γ α = 5 → Nonempty (oTwoQuot ↥(MulAction.stabilizer G α) ≃* ↥(Sz 0))

@[expose] def Fan66 (_ : FanTree Γ G) : Prop := ∀ T : Track Γ G, T.fixer = ⊥

@[expose] def Fan512 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  (∀ β : V, valence Γ β = 3 → ∀ z ∈ MulAction.stabilizer G β,
    (∀ g ∈ MulAction.stabilizer G β, g * z = z * g) → z * z = 1 → z = 1) ∧
  (∀ α : V, valence Γ α = 5 → L.z α ∈ ballStab Γ G 2 α) ∧
  (∀ β a b c : V, valence Γ β = 3 → Γ.neighborSet β = {a, b, c} → a ≠ b → a ≠ c → b ≠ c →
    L.z a * L.z b * L.z c = 1) ∧
  L.Unique

@[expose] def Fan517 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ α : V, valence Γ α = 5 →
    (L.zGroup 2 α ≤ nbrStab Γ G α ∧
      ∀ g ∈ L.zGroup 2 α, ∀ h ∈ L.zGroup 2 α, fcomm g h ∈ Subgroup.zpowers (L.z α)) ∧
    ∀ l₁ l₂ l₃ : V, Γ.dist α l₁ = 2 → Γ.dist α l₂ = 2 → Γ.dist α l₃ = 2 →
      L.z l₁ * L.z l₂ * L.z l₃ ∉ Subgroup.zpowers (L.z α)

end CFSG.Quasithin.Fan86
