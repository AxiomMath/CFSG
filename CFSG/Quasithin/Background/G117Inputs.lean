module

public import CFSG.Quasithin.Background.G9StmtsModels
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

@[expose] def AutHatM22Bound : Prop :=
  ∀ (N : Type) [Group N] [Finite N], IsHat N CFSG.Blueprint.NativeSporadic.M22 →
    Nat.card (MulAut N) ≤ 887040

@[expose] def G22DerivedFacts : Prop :=
  Nat.card ↥⁅CFSG.Open.quasithinG2 (GaloisField 2 1), CFSG.Open.quasithinG2 (GaloisField 2 1)⁆ =
      6048 ∧
    Nat.card (MulAut ↥⁅CFSG.Open.quasithinG2 (GaloisField 2 1),
      CFSG.Open.quasithinG2 (GaloisField 2 1)⁆) = 12096

@[expose] def A8OrthogonalFact : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (B : LinearMap.BilinForm (ZMod 2) V)
    (H Γ : Subgroup (GLV V)), Module.finrank (ZMod 2) V = 6 →
    IsPermCoreModule H (alternatingGroup (Fin 8)) → (∀ v, B v v = 0) →
    (∀ v, (∀ w, B v w = 0) → v = 0) → (∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w) → H ≤ Γ →
    (∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) → G112Concl5 B Γ

@[expose] def Om4Plus4Iso : Prop :=
  Nonempty (↥(StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) ≃*
    (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)))

@[expose] def A6NormalizerBound : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (H' R : Subgroup (GLV U)),
    IsPermCoreModule H' (alternatingGroup (Fin 6)) →
    (∀ r ∈ R, ∀ h ∈ H', r * h * r⁻¹ ∈ H') → Nat.card R ≤ 720

end G11

end CFSG.Quasithin
