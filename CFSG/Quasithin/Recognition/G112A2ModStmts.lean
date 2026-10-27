module

public import CFSG.Quasithin.Recognition.G112A2D12
public import CFSG.Milestones.ASVolI.G11

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def A2ClauseAt (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (V ≃ₗ[ZMod 2] V))
    (v₁ : V) : Prop :=
  ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
    v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁

@[expose] def G112Concl6Mod (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧ IsG2NaturalModule Γ (CFSG.Open.quasithinG2 (ZMod 2))

@[expose] def G112Concl7Mod (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    IsNaturalMatrixModule (fStarIn Γ) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) ∧
    ¬ X ≤ fStarIn Γ

@[expose] def G112Concl11Mod (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule (fStarIn Γ)

@[expose] def G112ConclusionMod (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Prop :=
  G112Concl1 Γ ∨ G112Concl2 Γ ∨ G112Concl3 Γ ∨ G112Concl4 Γ ∨ G112Concl5 B Γ ∨ G112Concl6Mod Γ ∨
    G112Concl7Mod Γ X ∨ G112Concl8 B Γ X ∨ IsG112Nine Γ ∨ IsG112Ten Γ X ∨ G112Concl11Mod Γ ∨
    G112Concl12 Γ X ∨ G112Concl13Mod Γ

@[expose] def G112ConclA2Mod : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → (G112ConclusionMod B Γ X ∨ G112ProposedU33 Γ) →
    4 ≤ Module.finrank (ZMod 2) V → A2ClauseAt B Γ X v₁

@[expose] def G112A2OpenConcl6 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → G112Concl6Mod Γ → A2ClauseAt B Γ X v₁

@[expose] def G112A2OpenConcl6U33 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → G112ProposedU33 Γ → A2ClauseAt B Γ X v₁

@[expose] def G112A2OpenConcl7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → G112Concl7Mod Γ X → A2ClauseAt B Γ X v₁

@[expose] def G112A2OpenConcl9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → IsG112Nine Γ → A2ClauseAt B Γ X v₁

@[expose] def G112A2OpenConcl11 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → G112Concl11Mod Γ → A2ClauseAt B Γ X v₁

end CFSG.Quasithin.G112A2
