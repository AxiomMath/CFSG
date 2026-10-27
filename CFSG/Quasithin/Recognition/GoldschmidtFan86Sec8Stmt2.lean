module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan83a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' →
    nbrStab Γ G α = Subgroup.closure (Set.range (D.y δ')) ⊔ (L.zGroup 2 α ⊔ D.calpha)

@[expose] def Fan83b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' → ∀ i j : Fin 5,
    fcomm (D.y δ' i) (L.z (D.alpha j)) = if i = j then 1 else L.z α

@[expose] def Fan83c (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α), D.calpha ≠ Subgroup.zpowers (L.z α) → ∀ (i : Fin 5) (l₁ l₂ : V),
    IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2 →
      Subgroup.closure {g | ∃ c ∈ D.calpha, g = fcomm (L.z l₁ * L.z l₂) c} =
        Subgroup.zpowers (L.z (D.alpha i))

@[expose] def Fan83d (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  (∀ (α : V) (D : D10Set L α) (i j : Fin 5), i ≠ j → ∀ l₁ l₂ m₁ m₂ : V,
      IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2 →
      IsZ2Pair Γ G α (D.alpha j) (D.beta j) m₁ m₂ 2 →
      ∃ e : Fin 2, fcomm (L.z l₁ * L.z l₂) (L.z m₁ * L.z m₂) =
        L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)) * L.z α ^ (e : ℕ)) ∧
  ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' → ∀ i j : Fin 5, i ≠ j →
    fcomm (D.y δ' i) (D.y δ' j) = L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))

@[expose] def Fan83e (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (δ' : V), D.IsYPair δ' → ∀ i j : Fin 5, i ≠ j →
    {v | v ∈ D.Delta4 ∧ (D.y δ' i * D.y δ' j) • v = v} =
      Γ.neighborSet α ∪ pathSet Γ (D.alpha (kstar i j)) (D.alpha (kstar j i)) ∪
        pathSet Γ α (D.alpha (midlab i j))

@[expose] def Fan83 (F : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  Fan83a F L ∧ Fan83b F L ∧ Fan83c F L ∧ Fan83d F L ∧ Fan83e F L

end CFSG.Quasithin.Fan86
