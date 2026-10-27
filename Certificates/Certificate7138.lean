
module

public import Certificates.Certificate7138Base

public import CFSG.Quasithin.H13.L32NSp4MainBase

public section

namespace Certificates

open CFSG.Quasithin CFSG.Quasithin.H13.Sp4Cert in
theorem certificate7138 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V},
    (∀ v, B v v = 0) → B.Nondegenerate → Module.finrank (ZMod 2) V = 4 →
    Γ ≤ CFSG.Quasithin.H13.KGCert.spGroup B → (10 ∣ Nat.card Γ ∨ 18 ∣ Nat.card Γ) →
    ∀ {W : Submodule (ZMod 2) V} {u w : V}, (∀ x ∈ W, x = 0 ∨ x = u ∨ x = w ∨ x = u + w) →
    u ∈ W → w ∈ W → u ≠ 0 → w ≠ 0 → u ≠ w → B u w = 0 →
    Nat.gcd (Nat.card Γ) 16 ∣ Nat.card ↥(Γ ⊓ stabW W) →
    (∃ y ∈ Γ, y ∈ stabW W ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧ ∃ x ∈ W, y x ≠ x) →
    ¬ Γ ≤ stabW W →
    (∃ t ∈ Γ, t ∈ stabW W ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ ∃ x ∈ W, t x ≠ x) →
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
  fun halt hnd hd hΓ h1018 => CFSG.Quasithin.H13.Sp4Cert.sp4_classify_of halt hnd hd hΓ h1018

end Certificates
