module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] def Input14610PermTuOut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    ((IsAlt 6 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 5) ∨
      (IsAlt 7 (OTwoQuot K) ∧ Nat.card (wOf1469 K) = 2 ^ 6)) →
    T ⊓ I = tU T u → Nat.card (conjClosure (VZ T M) I₂) ≠ 2 ^ 3 → u ∉ wOf1469 K → False

@[expose] def Input14610PermA7Fixed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I I₂ K : Subgroup G),
    Facts14610 T M H u I I₂ → Concl14610List T M I I₂ K →
    IsAlt 7 (OTwoQuot K) → Nat.card (wOf1469 K) = 2 ^ 6 →
    wOf1469 K ⊓ Subgroup.centralizer (K : Set G) = ⊥

end CFSG.Quasithin
