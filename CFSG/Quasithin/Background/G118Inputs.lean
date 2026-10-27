module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace G118

@[expose] def SL24IsoA5 : Prop :=
  Nonempty (↥(StatedSL 2 (GaloisField 2 2)) ≃* ↥(alternatingGroup (Fin 5)))

@[expose] def Sp44RankInput : Prop :=
  ∀ (I : Type) [AddCommGroup I] [Module (ZMod 2) I] [Finite I] (H' : Subgroup (GLV I)),
    IsNaturalMatrixModule H' ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ →
    ∀ (A : Subgroup (GLV I)), IsElemAbelian 2 A → (∀ a ∈ A, ∀ h ∈ H', a * h * a⁻¹ ∈ H') →
      (∃ a ∈ A, ∃ f ∈ endCommutant H',
        ¬ ((a : I →ₗ[ZMod 2] I) * f = f * (a : I →ₗ[ZMod 2] I))) → Nat.card ↥A ≤ 2 ^ 4

@[expose] def IsScalarAut {F U : Type} [Field F] [AddCommGroup U] [Module F U]
    (c : U ≃ₗ[F] U) : Prop :=
  ∃ a : F, ∀ u : U, c u = a • u

@[expose] def GL24SubInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (U : Type) [AddCommGroup U] [Module F U] [Module.Finite F U],
    Nat.card F = 4 → Module.finrank F U = 2 →
    ∀ (Ĉ : Subgroup (U ≃ₗ[F] U)) (τ : F ≃+* F) (σ : U →ₛₗ[(τ : F →+* F)] U)
      (hσ : Function.Bijective σ), τ ≠ RingEquiv.refl F →
      (∀ p : Projectivization F U,
        Projectivization.map σ hσ.1 (Projectivization.map σ hσ.1 p) = p) →
      (∀ c ∈ Ĉ, ∃ c' ∈ Ĉ, ∀ u : U, c' (σ u) = σ (c u)) →
      (∀ N : Subgroup ↥Ĉ, N.Normal → IsPGroup 2 N → N = ⊥) →
      (∃ y ∈ Ĉ, y ≠ 1 ∧ y * y = 1) →
      ((∀ c ∈ Ĉ, IsScalarAut c → c = 1) ∧
        (Nonempty (↥Ĉ ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (↥Ĉ ≃* ↥(alternatingGroup (Fin 5))))) ∨
      (∃ ζ ∈ Ĉ, ζ ≠ 1 ∧ IsScalarAut ζ ∧
        ∃ c ∈ Ĉ, c * c * c = 1 ∧ ¬ IsScalarAut c)

end G118

end G11

end CFSG.Quasithin
