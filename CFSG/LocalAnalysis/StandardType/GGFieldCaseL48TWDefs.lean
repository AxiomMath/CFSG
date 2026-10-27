module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Homocyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

@[expose] def GGL48NormalInputS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def GGL48LFieldIOneInputS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      x ∉ ⁅Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
          Subgroup.centralizer ({x} : Set G) ⊓
            Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G)⁆ ⊔
        ggL48U2 x U₁ ⊔ (L ⊓ Subgroup.centralizer
          ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G))

@[expose] def GGL48TorusWeylCentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      ∀ c ∈ L ⊓ Subgroup.centralizer
          ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
        (∃ k : ℕ, c ^ p ^ k = 1) →
      ∃ (S : Subgroup G) (W : Set G), IsPGroup p S ∧
        S ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        S ≤ J ∧
        W ⊆ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set G))

@[expose] def GGL48InnerKInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → U ⊓ K ≤ U₁

@[expose] def GGL48AutomizerMetaAt {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (x : G) : Prop :=
  ∀ (M E : Subgroup G) (h : G),
    M ≤ E → E ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) →
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ⊓
        Subgroup.centralizer (Bs : Set G) ≤ M →
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
        Subgroup.normalizer (M : Set G) →
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
        Subgroup.normalizer (E : Set G) →
    (∀ e ∈ E, ∃ k : ℕ, e ^ p ^ k ∈ M) →
    h ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) →
    (orderOf h).Coprime p →
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (Bs : Set G) ≤
        E ⊔ Subgroup.zpowers h →
    E ≤ M

@[expose] def GGL48HomocyclicOrMetaInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → GGL46 p Bs x X U U₁ →
      GGL48Homocyclic p U₁ ∨ GGL48AutomizerMetaAt p Bs x

end CFSG.StandardType
