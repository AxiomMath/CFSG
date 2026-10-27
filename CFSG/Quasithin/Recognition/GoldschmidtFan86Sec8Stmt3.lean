module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin CFSG.Open CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan84a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α), IsCyclic ↥D.calpha ∧ Nat.card ↥D.calpha ≤ 4

@[expose] def Fan85 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' → prodFive (D.y δ') = 1

@[expose] def Fan86a (_ : FanTree Γ G) : Prop :=
  ∀ α : V, valence Γ α = 5 → ∀ g ∈ nbrStab Γ G α, g ≠ 1 → orderOf g = 2 ∨ orderOf g = 4

@[expose] def IsW1Elem {L : ZLab Γ G} {α : V} (D : D10Set L α) (w : G) : Prop :=
  w ∈ (D.P 0).stab G ∧ orderOf w = 4 ∧ w⁻¹ * D.x * w = D.x ^ 2 ∧
    (w * w = L.z (D.delta 0) ∨ w * w = L.z (D.delta 0) * L.z α)

@[expose] def Fan86b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α), (∃ w : G, IsW1Elem D w) ∧
    ∀ w : G, IsW1Elem D w → ∀ (i : Fin 5) (m : ℕ), m ≤ 4 →
      w⁻¹ • (D.P i).vert m = (D.P (2 * i)).vert m

@[expose] def Fan86c (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (w : G), IsW1Elem D w →
    MulAction.stabilizer G α = Subgroup.closure {D.x, w} ⊔ nbrStab Γ G α ∧
    Nonempty (↥(Subgroup.closure {D.x, w}) ≃* ↥(Sz 0))

@[expose] def Fan86abc (F : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  Fan86a F ∧ Fan86b F L ∧ Fan86c F L

@[expose] def Fan87 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' → ∀ i j : Fin 5, i ≠ j →
    ∀ w : G, (∀ v ∈ pathSet Γ (D.alpha i) (D.alpha j), w • v = v) → orderOf w = 4 →
      (∃ e₁ e₂ e₃ : Fin 2, w * w = L.z (D.alpha i) ^ (e₁ : ℕ) * L.z (D.alpha j) ^ (e₂ : ℕ) *
        L.z α ^ (e₃ : ℕ)) →
      (∃ v ∈ L.zGroup 2 α, ∃ e : Fin 2,
          w = D.y δ' (kstar i j) * D.y δ' (kstar j i) * v ∧
            w * w = L.z (D.alpha i) * L.z (D.alpha j) * L.z α ^ (e : ℕ)) ∨
      (∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, orderOf c = 4 ∧ ∃ e : Fin 2,
          w = D.y δ' (kstar i j) * D.y δ' (midlab i j) * v * c ∧
            w * w = L.z (D.alpha i) * L.z α ^ (e : ℕ)) ∨
      (∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, orderOf c = 4 ∧ ∃ e : Fin 2,
          w = D.y δ' (kstar j i) * D.y δ' (midlab i j) * v * c ∧
            w * w = L.z (D.alpha j) * L.z α ^ (e : ℕ)) ∨
      (∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, orderOf c = 4 ∧ w = v * c ∧ w * w = L.z α)

end CFSG.Quasithin.Fan86
