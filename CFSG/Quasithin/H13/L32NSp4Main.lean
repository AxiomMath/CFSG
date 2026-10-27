
module


public import Certificates.Certificate7138

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert CFSG.ComponentClassification.PresentationLocal Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {b : Module.Basis (Fin 4) (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {s : Node}

theorem sp4_classify {B : LinearMap.BilinForm (ZMod 2) V}
    (halt : ∀ v, B v v = 0) (hnd : B.Nondegenerate) (hd : Module.finrank (ZMod 2) V = 4)
    (hΓ : Γ ≤ KGCert.spGroup B) (h1018 : 10 ∣ Nat.card Γ ∨ 18 ∣ Nat.card Γ)
    {W : Submodule (ZMod 2) V} {u w : V} (hW : ∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w)
    (huW : u ∈ W) (hwW : w ∈ W) (hu : u ≠ 0) (hw : w ≠ 0) (huw : u ≠ w) (hB : B u w = 0)
    (hT : Nat.gcd (Nat.card Γ) 16 ∣ Nat.card ↥(Γ ⊓ stabW W))
    (h3 : ∃ y ∈ Γ, y ∈ stabW W ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧ ∃ x ∈ W, y x ≠ x)
    (hne : ¬ Γ ≤ stabW W)
    (h2 : ∃ t ∈ Γ, t ∈ stabW W ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ ∃ x ∈ W, t x ≠ x) :
    (Nat.card Γ = 18 ∧ HasE9 Γ) ∨
    (Nonempty (↥Γ ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧ HasE9 Γ ∧
      Nat.card ↥(Γ ⊓ fixW W) = 2 ∧
      ∃ X : Subgroup (V ≃ₗ[ZMod 2] V), X ≤ Γ ∧ Nat.card X = 6 ∧
        (∃ α ∈ X, ∃ β ∈ X, α * β ≠ β * α) ∧ Γ ≤ Subgroup.normalizer (X : Set _) ∧
        Γ ⊓ fixW W ≤ X ∧
        ∀ y ∈ Γ, y ∈ stabW W → y ∈ X → y ≠ 1 → y ^ 3 = 1 → ∀ x ∈ W, y x = x) ∨
    (Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) ∧
      (∃ (φ : ↥Γ ≃* RuType.SigmaL2F4) (ψ : V ≃+ (Fin 2 → RuType.F4)),
        ∀ (γ : ↥Γ) (v : V), ψ ((γ : V ≃ₗ[ZMod 2] V) v) = RuType.sigmaAct (φ γ) (ψ v)) ∧
      (∀ γ ∈ Γ ⊓ fixW W, γ ∈ (CFSG.Open.genFittingLayer ↥Γ).map Γ.subtype) ∧
      (∀ t ∈ Γ, t ∈ stabW W → t ≠ 1 → t ^ 2 = 1 → (∃ x ∈ W, t x ≠ x) →
        Nat.card ↥(Γ ⊓ (fixW W ⊓ Subgroup.centralizer {t})) = 2) ∧ QuadMoved B Γ u w) ∨
    (((Nonempty (↥Γ ≃* ↥(alternatingGroup (Fin 6))) ∧ Nat.card ↥(Γ ⊓ fixW W) = 4) ∨
      (Nonempty (↥Γ ≃* Equiv.Perm (Fin 6)) ∧ Nat.card ↥(Γ ⊓ fixW W) = 8 ∧
        ∀ γ ∈ Γ, (∀ f ∈ Γ ⊓ fixW W, f * γ = γ * f) → γ ∈ fixW W)) ∧ QuadMoved B Γ u w) :=
  Certificates.certificate7138 halt hnd hd hΓ h1018 hW huW hwW hu hw huw hB hT h3 hne h2

end CFSG.Quasithin.H13.Sp4Cert
