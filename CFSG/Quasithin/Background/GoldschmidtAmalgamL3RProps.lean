module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

@[expose] def BGeInput (n : ℕ) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → Nat.card (conjClosure V B) = 8 → ¬ n ≤ critDist (A ⊔ B) A B V

@[expose] def B9Input : Prop := BGeInput.{u} 9

@[expose] def B5Input : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → Nat.card (conjClosure V B) = 8 → critDist (A ⊔ B) A B V ≠ 5

@[expose] def SymConfigFive {D : Type*} [Group D] (A B : Subgroup D) (V : Subgroup D)
    (p : ℕ → CosetGeom (A ⊔ B) A B) (γ : CosetGeom (A ⊔ B) A B) : Prop :=
  p 0 = γ₀ (A ⊔ B) A B ∧ IsGeo p 5 ∧ ¬ V ≤ ballStab 1 (p 5) ∧
    (graph (A ⊔ B) A B).Adj (p 5) γ ∧ ¬ Vv V γ ≤ ballStab 1 (p 1)

@[expose] def B5SymInput : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (A B : Subgroup D) (z : D) (V : Subgroup D),
    GoldHyp3 A B z V → Nat.card (conjClosure V B) = 8 → critDist (A ⊔ B) A B V = 5 →
      ∀ (p : ℕ → CosetGeom (A ⊔ B) A B) (γ : CosetGeom (A ⊔ B) A B), ¬ SymConfigFive A B V p γ

end GoldAmL3

end F6

end CFSG.Quasithin
