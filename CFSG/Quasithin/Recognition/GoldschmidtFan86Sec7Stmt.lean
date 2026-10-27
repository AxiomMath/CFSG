module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ZLab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def ZLab.calpha (L : ZLab Γ G) (P : Arc Γ 8) : Subgroup G :=
  nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({L.z (P.vert 0) * L.z (P.vert 8)} : Set G)

@[expose] def Fan71a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ P : Arc Γ 8, valence Γ (P.vert 0) = 5 →
    Nonempty (↥(Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G)) ≃*
        DihedralGroup 5) ∧
    ∀ x ∈ Subgroup.closure ({L.z (P.vert 0), L.z (P.vert 8)} : Set G), orderOf x = 5 →
      nbrStab Γ G (P.vert 4) ⊓ Subgroup.centralizer ({x} : Set G) = P.stab G

@[expose] def Fan71b (_ : FanTree Γ G) : Prop := TransGe Γ G 7 ∧ SingGe Γ G 8

@[expose] def Fan71c (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  (∀ l, valence Γ l = 5 → fixedPts (V := V) (L.z l) = {v | Γ.dist l v ≤ 4}) ∧
  (∀ a b, valence Γ a = 5 → valence Γ b = 5 → a ≠ b → L.z a ≠ L.z b) ∧
  (∀ a b c, valence Γ a = 5 → valence Γ b = 5 → valence Γ c = 5 → a ≠ b → a ≠ c → b ≠ c →
    (¬ ∃ β, ({a, b, c} : Set V) = Γ.neighborSet β) → L.z a * L.z b * L.z c ≠ 1)

@[expose] def Fan72a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (l : Fin 5 → V), valence Γ α = 5 →
    (∀ i, Γ.dist α (l i) = 2 ∧ valence Γ (l i) = 5) → (∀ i j, i ≠ j → Γ.dist (l i) (l j) = 4) →
    (List.ofFn fun i => L.z (l i)).prod = 1 ∨ (List.ofFn fun i => L.z (l i)).prod = L.z α

@[expose] def Fan72b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ α : V, valence Γ α = 5 → Nat.card ↥(L.zGroup 2 α) = 2 ^ 5

@[expose] def Fan73a (_ : FanTree Γ G) : Prop :=
  ∀ α : V, valence Γ α = 5 →
    (ballStab Γ G 2 α).relIndex (nbrStab Γ G α) = 2 ^ 4 ∧
    (∀ g ∈ nbrStab Γ G α, g * g ∈ ballStab Γ G 2 α) ∧
    (∀ g ∈ nbrStab Γ G α, ∀ h ∈ nbrStab Γ G α, g * h * g⁻¹ * h⁻¹ ∈ ballStab Γ G 2 α) ∧
    (∀ N : Subgroup G, ballStab Γ G 2 α ≤ N → N ≤ nbrStab Γ G α →
      (∀ g ∈ MulAction.stabilizer G α, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
        N = ballStab Γ G 2 α ∨ N = nbrStab Γ G α) ∧
    ¬ (∀ g ∈ MulAction.stabilizer G α, ∀ k ∈ nbrStab Γ G α,
        g * k * g⁻¹ * k⁻¹ ∈ ballStab Γ G 2 α)

@[expose] def Fan73b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ P : Arc Γ 8, valence Γ (P.vert 4) = 5 →
    ballStab Γ G 2 (P.vert 4) = L.zGroup 2 (P.vert 4) ⊔ L.calpha P ∧
    L.zGroup 2 (P.vert 4) ⊓ L.calpha P = Subgroup.zpowers (L.z (P.vert 4))

@[expose] def Fan74 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ P : Arc Γ 8, valence Γ (P.vert 4) = 5 →
    ballStab Γ G 3 (P.vert 4) ≤ L.calpha P ∧
    (ballStab Γ G 3 (P.vert 4)).relIndex (L.calpha P) ≤ 2 ∧
    ballStab Γ G 5 (P.vert 4) = ⊥ ∧ ∀ β, Γ.Adj (P.vert 4) β → ballStab Γ G 4 β = ⊥

@[expose] def Fan75 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ P : Arc Γ 8, valence Γ (P.vert 4) = 5 →
    ballStab Γ G 3 (P.vert 4) = Subgroup.zpowers (L.z (P.vert 4)) ∧
    ballStab Γ G 4 (P.vert 4) = Subgroup.zpowers (L.z (P.vert 4)) ∧ Nat.card ↥(L.calpha P) ≤ 4

@[expose] def Fan7 (F : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  Fan71a F L ∧ Fan71b F ∧ Fan71c F L ∧ Fan72a F L ∧ Fan72b F L ∧ Fan73a F ∧ Fan73b F L ∧
    Fan74 F L ∧ Fan75 F L

end CFSG.Quasithin.Fan86
