module

public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

structure Conf {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  hyp : G111Hyp B Γ v₁ W X X₀
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  h108 : G108Hyp B Γ v₁ W X X₀ L
  numConj : numConjugates Γ L ≤ 2

@[expose] def NoConfigM12 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      IsPermCoreModule (normalClosure Γ L) CFSG.Blueprint.NativeSporadic.M12 →
      Nat.card X = 16 → Module.finrank (ZMod 2) V = 10 →
      (∀ x ∈ Γ, (∀ h ∈ normalClosure Γ L, x * h = h * x) → x = 1) → False

@[expose] def NoConfigL2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      ∀ n : ℕ, 3 ≤ n →
        IsNaturalMatrixModule (normalClosure Γ L) (StatedSL 2 (GaloisField 2 n)) → False

@[expose] def NoConfigOm4Minus : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      ∀ a : ℕ, 2 ≤ a → ∀ b c : GaloisField 2 a, (∀ s : GaloisField 2 a, s ^ 2 + b * s + c ≠ 0) →
        IsNaturalMatrixModule (normalClosure Γ L)
          (StatedOmega (StatedQuadMinus 2 (GaloisField 2 a) b c)) → False

@[expose] def NoConfigSp4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      ∀ n : ℕ, 2 ≤ n →
        IsNaturalMatrixModule (normalClosure Γ L)
          ⁅StatedSp 2 (GaloisField 2 n), StatedSp 2 (GaloisField 2 n)⁆ → False

@[expose] def NoConfigG2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      ∀ n : ℕ, 2 ≤ n →
        IsG2NaturalModule (normalClosure Γ L)
          ⁅CFSG.Open.quasithinG2 (GaloisField 2 n), CFSG.Open.quasithinG2 (GaloisField 2 n)⁆ →
          False

@[expose] def NoConfigOm4Plus : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      ∀ n : ℕ, 3 ≤ n →
        IsNaturalMatrixModule (normalClosure Γ L)
          (StatedOmega (StatedQuadPlus 2 (GaloisField 2 n))) → False

@[expose] def NoConfigOm4PlusFour : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      IsNaturalMatrixModule (normalClosure Γ L)
        (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) → X ≤ normalClosure Γ L → False

@[expose] def NoConfigSp4Two : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      IsNaturalMatrixModule (normalClosure Γ L)
        ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ →
      (∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)) → False

@[expose] def NoConfigOm4MinusTwo : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      ∀ b c : GaloisField 2 2, (∀ s : GaloisField 2 2, s ^ 2 + b * s + c ≠ 0) →
        IsNaturalMatrixModule (normalClosure Γ L)
          (StatedOmega (StatedQuadMinus 2 (GaloisField 2 2) b c)) →
        (∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)) → False

@[expose] def NoConfigG2Two : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    Conf B Γ v₁ W X X₀ L → G116Props B Γ v₁ X L ⊤ →
      IsG2NaturalModule (normalClosure Γ L)
        ⁅CFSG.Open.quasithinG2 (GaloisField 2 2), CFSG.Open.quasithinG2 (GaloisField 2 2)⁆ →
      (∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)) → False

end SzG11S

end G11

end CFSG.Quasithin
