module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan51a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (a : ℤ) (n : ℕ), 2 ≤ n → ¬ LineSingLe Γ G ℓ (n - 1) →
    ∀ d : ℕ, 1 ≤ d → d + 1 ≤ n →
      ∃ x ∈ Subgroup.closure (ℓ.edgeCirc a ∪ ℓ.edgeCirc (a + ((n - 1 : ℕ) : ℤ))) ⊓
        MulAction.stabilizer G (ℓ.vert (a + d)), orderOf x = valence Γ (ℓ.vert (a + d))

@[expose] def Fan51b (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (a : ℤ) (n : ℕ), 1 ≤ n → ¬ LineSingLe Γ G ℓ (n - 1) →
    ¬ (n = 4 ∧ LineSingLe Γ G ℓ 4 ∧ valence Γ (ℓ.vert a) = 3 ∧ valence Γ (ℓ.vert (a + n)) = 3) →
    Subgroup.closure (ℓ.edgeCirc a ∪ ℓ.edgeCirc (a + ((n - 1 : ℕ) : ℤ))) ≤
        Subgroup.closure ((nbrStab Γ G (ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert (a + n))) ∧
      (valence Γ (ℓ.vert a) = 3 →
        Subgroup.closure {g | ∃ i : ℕ, 1 ≤ i ∧ i + 1 ≤ n ∧ g ∈ ℓ.edgeStab (G := G) (a + i)} ≤
          Subgroup.closure ((nbrStab Γ G (ℓ.vert a) : Set G) ∪ nbrStab Γ G (ℓ.vert (a + n))))

@[expose] def Fan53a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z : G) (a b tL tR : ℤ), z ∈ ℓ.ZZ → ℓ.IsCoreFix z a b tL tR →
    1 ≤ tR - b ∧ 1 ≤ a - tL ∧ (valence Γ (ℓ.vert tR) ≠ 3 → 2 ≤ tR - b) ∧
      (valence Γ (ℓ.vert tL) ≠ 3 → 2 ≤ a - tL)

@[expose] def Fan53b (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z : G) (a b : ℤ), z ∈ ℓ.ZZ → ℓ.IsCore z a b → ℓ.IsCoreC z a b

@[expose] def Fan53c (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z : G) (a b : ℤ), z ∈ ℓ.Zc → ℓ.IsCoreC z a b → b - a ≤ 2

@[expose] def Fan54 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z : G) (a b : ℤ), z ∈ ℓ.Zc → ℓ.IsCoreC z a b →
    ∀ δ α : ℤ, (δ = b ∧ α = b - 1 ∨ δ = b + 1 ∧ α = b ∨ δ = a ∧ α = a + 1 ∨ δ = a - 1 ∧ α = a) →
      ∀ x ∈ MulAction.stabilizer G (ℓ.vert δ), x ∉ MulAction.stabilizer G (ℓ.vert α) →
        x * z ≠ z * x

@[expose] def Fan55h1 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ), z ∈ ℓ.Zc → z' ∈ ℓ.Zc →
    ℓ.IsCoreCFix z a b tL tR → ℓ.IsCoreCFix z' a' b' tL' tR' → (a' = tR ∨ a' = tR + 1) → b ≤ tL'

@[expose] def Fan55h2 (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ), z ∈ ℓ.Zc → z' ∈ ℓ.Zc →
    ℓ.IsCoreCFix z a b tL tR → ℓ.IsCoreCFix z' a' b' tL' tR' → (tL' = b ∨ tL' = b + 1) → tR ≤ a'

@[expose] def Fan55a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ),
    z ∈ T.line.Zc → z' ∈ T.line.Zc → T.line.IsCoreCFix z a b tL tR →
    T.line.IsCoreCFix z' a' b' tL' tR' →
    ∃ m : ℤ, T.line.InPos z (T.τ ^ m * z' * T.τ ^ (-m)) a b tL tR
      (a' + 2 * m) (b' + 2 * m) (tL' + 2 * m) (tR' + 2 * m)

@[expose] def Fan55b (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a b tL tR a' b' : ℤ), z ∈ T.line.Zc →
    T.line.IsCoreCFix z a b tL tR → T.line.IsCoreC z a' b' → a' = a ∧ b' = b

@[expose] def Fan55c (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ),
    z ∈ T.line.Zc → z' ∈ T.line.Zc → T.line.IsCoreCFix z a b tL tR →
    T.line.IsCoreCFix z' a' b' tL' tR' → |(tR - b) - (a' - tL')| ≤ 1

@[expose] def Fan57a (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (ℓ : Line Γ) (z z' : G) (a b tL tR a' b' tL' tR' : ℤ), z ∈ ℓ.ZZ → z' ∈ ℓ.ZZ →
    ℓ.IsCoreFix z a b tL tR → ℓ.IsCoreFix z' a' b' tL' tR' → b = tL' →
    fcomm z z' ≠ 1 ∧ fcomm z z' * fcomm z z' = 1 ∧ fcomm z z' ∈ Cen (ℓ.edgeCirc b)

@[expose] def Fan58b (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ (T : Track Γ G) (z : G) (a b tL tR : ℤ), z ∈ T.line.ZZ →
    T.line.IsCoreFix z a b tL tR → tR - b ≤ 2 → a - tL ≤ 2 → b - a = 2 ∧ tR - b = a - tL

end CFSG.Quasithin.Fan86
