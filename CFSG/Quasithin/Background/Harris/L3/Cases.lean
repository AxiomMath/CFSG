module

public import CFSG.Quasithin.Background.Harris.L3.Setup
public import CFSG.Quasithin.Background.HL3NineModel

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Open Matrix
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def NatShape (L : Subgroup (GLV V)) {F : Type} [Field F] (π : SL(3, F) →* ↥L) : Prop :=
  ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : V ≃+ (Fin 3 → F),
    ∀ g w, E (repOfHom L π g w) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E w

@[expose] def HermShape (L : Subgroup (GLV V)) {F : Type} [Field F] [Finite F] [CharP F 2]
    (π : SL(3, F) →* ↥L) (k : ℕ) : Prop :=
  ∃ hK : Nat.card F = (2 ^ k) ^ 2, ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧
    ∃ E : Multiplicative V ≃* CFSG.Quasithin.H.L3Nine.HMod k F, ∀ g u,
      E (Multiplicative.ofAdd (repOfHom L π g u)) =
        CFSG.Quasithin.H.L3Nine.rho hK (ψ g) (E (Multiplicative.ofAdd u))

@[expose] def Case8Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m f : ℕ), OneCompSetting Γ A L m → 1 ≤ f →
    ∀ π : SL(3, GaloisField 2 f) →* ↥L, Function.Surjective π → m ≤ 2 * f → NatShape L π →
    G93Case8 L m

@[expose] def Case17Input : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ A L : Subgroup (GLV V))
    (m k : ℕ), OneCompSetting Γ A L m → (k = 1 ∨ k = 2) →
    ∀ π : SL(3, GaloisField 2 (2 * k)) →* ↥L, Function.Surjective π → m ≤ 4 * k →
    HermShape L π k → G93Case17 L m

@[expose] def NotSelfDualInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (L : Subgroup (GLV V)) (f : ℕ),
    1 ≤ f → ∀ π : SL(3, GaloisField 2 f) →* ↥L, Function.Surjective π → IsIrr L ⊤ →
    (NatShape L π ∨ ∃ k, HermShape L π k) → ¬ SelfDual L ⊤

end CFSG.Quasithin.G11.Harris.L3
