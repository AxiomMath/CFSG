module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan81 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ α a₀ β δ δ' : V, valence Γ α = 5 → IsZ2Pair Γ G α a₀ β δ δ' 2 →
    {v | Γ.dist α v ≤ 4 ∧ (L.z δ * L.z δ') • v = v} =
      {v | Γ.dist a₀ v ≤ 2 ∨ Γ.dist β v ≤ 2}

@[expose] def Fan82a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α), prodFive (fun i => L.z (D.alpha i)) = 1

@[expose] def Fan82b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (i j : Fin 5), i ≠ j →
    {v | v ∈ D.Delta4 ∧ (L.z (D.alpha i) * L.z (D.alpha j)) • v = v} =
      pathSet Γ (D.alpha i) (D.alpha j) ∪ pathSet Γ (D.xi (kstar i j)) (D.xi (kstar j i)) ∪
        pathSet Γ α (D.delta (midlab i j))

@[expose] def Fan82c (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α) (i j : Fin 5), i ≠ j →
    L.z (D.alpha i) * L.z (D.alpha j) ∈ ballStab Γ G 3 (D.beta (midlab i j)) ∧
    L.z (D.alpha i) * L.z (D.alpha j) ∉ nbrStab Γ G (D.delta (midlab i j))

@[expose] def Fan82 (F : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  Fan82a F L ∧ Fan82b F L ∧ Fan82c F L

end CFSG.Quasithin.Fan86
