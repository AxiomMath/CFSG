module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Fan28 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), IsSylowTwoOf S ⊤ →
    Nonempty (oTwoQuot H ≃* Equiv.Perm (Fin 3)) →
    (∀ K : Subgroup H, K ≤ S → K ≠ ⊥ → (K.subgroupOf S).Characteristic → ¬ K.Normal) →
    ∃ n : ℕ, (n = 3 ∨ n = 4) ∧ ∃ (C : Type) (_ : Group C) (_ : Finite C), IsPGroup 2 C ∧
      Nonempty (H ≃* Equiv.Perm (Fin n) × C)

@[expose] def Fan41Three {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (_ : FanTree Γ G) : Prop :=
  ∀ (a b c : V) (L : Subgroup G), Γ.Adj a b → a ≠ c → L ∈ LamSet Γ G a b c →
    valence Γ a = 3 → Fan28 →
    ∃ n : ℕ, (n = 3 ∨ n = 4) ∧ ∃ (C : Type) (_ : Group C) (_ : Finite C), IsPGroup 2 C ∧
      Nonempty (↥(L ⊓ MulAction.stabilizer G a) ≃* Equiv.Perm (Fin n) × C)

end CFSG.Quasithin.Fan86
