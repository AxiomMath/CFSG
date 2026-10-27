module

public import CFSG.LocalAnalysis.StandardType.GGPropFourOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGL43 (Bs : Subgroup G) (x : G) (X : Subgroup G) : Prop :=
  x ∉ Bs ⊓ Subgroup.centralizer (X : Set G) ∧
    Bs = (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x

@[expose] def GGL44i (p : ℕ) (Bs : Subgroup G) (x : G) (X : Subgroup G) : Prop :=
  (∀ g ∈ X, g * x = x * g → g ∈ Subgroup.centralizer (Bs : Set G)) ∧
    (∀ g ∈ X, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
    (∀ g ∈ X, ∀ h ∈ X, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
    ∀ g ∈ X, g ^ p ∈ Subgroup.centralizer (Bs : Set G)

@[expose] def GGTableBModule (p : ℕ) (Bs : Subgroup G) (x : G) (L B₂ : Subgroup G) : Prop :=
  x ∈ B₂ ∧ B₂ ≤ Bs ∧ Nat.card Bs ≤ p * Nat.card B₂ ∧
    (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ B₂, n * s * n⁻¹ ∈ B₂) ∧
    (∀ S : Subgroup G, Subgroup.zpowers x ≤ S → S ≤ B₂ →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = Subgroup.zpowers x ∨ S = B₂) ∧
    ∀ S T : Subgroup G, Subgroup.zpowers x ≤ S → Subgroup.zpowers x ≤ T →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      (∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ t ∈ T, n * t * n⁻¹ ∈ T) →
      S ⊓ T = Subgroup.zpowers x → S ⊔ T = Bs → S = Subgroup.zpowers x ∨ T = Subgroup.zpowers x

@[expose] def GGL44ii (Bs : Subgroup G) (x : G) (X B₂ : Subgroup G) : Prop :=
  (∀ b : G, b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b) ∨
    (B₂ < Bs ∧ ∀ b : G, b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ B₂ ↔
      ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = b)

@[expose] def GGL44iii (p : ℕ) (B Bs : Subgroup G) (x : G) (D J X : Subgroup G) (d y : G)
    (K : Subgroup G) : Prop :=
  D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Subgroup.zpowers d ∧ d ≠ 1 ∧
    GGNbr p B x D J y K ∧ Subgroup.zpowers y = Subgroup.zpowers d ∧
    LargeEvenMarking K (fun _ _ _ I F θ => Bs ≤ Subgroup.normalizer (K : Set G) ∧
      (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
        LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
      ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))

@[expose] def GGL45Setup (p : ℕ) (Bs X U : Subgroup G) : Prop :=
  U ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
    IsPGroup p U ∧
    (∀ Q : Subgroup G,
      Q ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) →
      IsPGroup p Q → U ≤ Q → Q = U) ∧
    Bs ≤ U

@[expose] def GGInnerDiagPart (U K U₁ : Subgroup G) : Prop :=
  U ≤ Subgroup.normalizer (K : Set G) ∧ U₁ ≤ U ∧
    LargeEvenMarking K (fun _ _ _ I _ θ => ∀ u ∈ U, u ∈ U₁ ↔
      ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ)

@[expose] def GGL46 (p : ℕ) (Bs : Subgroup G) (x : G) (X U U₁ : Subgroup G) : Prop :=
  IsMulCommutative U₁ ∧
    (∃ s : ℕ, 2 ≤ s ∧ (∀ u ∈ U₁, u ^ p ^ s = 1) ∧ (∃ u ∈ U₁, orderOf u = p ^ s) ∧
      (∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
        ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) ∧
      ∃ (H : Subgroup G) (r : ℕ), H ≤ U₁ ∧ (∀ h ∈ H, h ^ p ^ s = 1) ∧
        Nat.card H = p ^ (s * r) ∧
        Nat.card (H ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) = p ^ r ∧
        Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ p ^ (r + 1)) ∧
    (∀ A ∈ thompsonAbelianSubgroups U, A = U₁) ∧
    (∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1) ∧
    (∀ u ∈ U, u ^ p = 1 → u ∈ Bs) ∧
    GGOpAutTrivial p (Bs ⊓ Subgroup.centralizer (X : Set G))

@[expose] def GGFieldCaseSetup (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X B₂ : Subgroup G)
    (d y : G) (K U U₁ : Subgroup G) : Prop :=
  GGFieldCase p B Bs x L D J X ∧ GGTableBModule p Bs x L B₂ ∧ GGL43 Bs x X ∧ GGL44i p Bs x X ∧
    GGL44ii Bs x X B₂ ∧ GGL44iii p B Bs x D J X d y K ∧ GGL45Setup p Bs X U ∧ GGInnerDiagPart U K U₁ ∧
    Subgroup.normalizer (U : Set G) ⊓
        Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (U₁ : Set G)

end Defs

@[expose] def GGTableBModuleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∃ B₂ : Subgroup G, GGTableBModule p Bs x L B₂

@[expose] def GGL43Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G),
    GGFieldCase p B Bs x L D J X → GGL43 Bs x X

@[expose] def GGL44iiiInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCase p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      ∃ (d y : G) (K : Subgroup G), GGL44iii p B Bs x D J X d y K

@[expose] def GGL45Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U : Subgroup G),
    GGFieldCase p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      GGL44iii p B Bs x D J X d y K → GGL45Setup p Bs X U →
      U ≤ Subgroup.normalizer (K : Set G) →
      ∃ U₁ : Subgroup G, GGInnerDiagPart U K U₁ ∧
        Subgroup.normalizer (U : Set G) ⊓
            Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ≤
          Subgroup.normalizer (U₁ : Set G)

@[expose] def GGL46Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁

@[expose] def GGL47Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R →
        R ≤ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) →
        (∀ Q : Subgroup G,
          Q ≤ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) →
          IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → ∀ A ∈ thompsonAbelianSubgroups R, ⁅⁅U₁, A⁆, A⁆ = ⊥ → A ≤ U

@[expose] def GGL48Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        x ∉ ⁅Subgroup.normalizer (U₁ : Set G), Subgroup.normalizer (U₁ : Set G)⁆

end CFSG.StandardType

end
