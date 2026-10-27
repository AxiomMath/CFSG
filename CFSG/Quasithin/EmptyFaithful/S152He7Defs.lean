module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

@[expose] def PureTransIi : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), (n = 4 ∨ n = 5) → IsAutLnTwo n Y → SQTKGroup Y →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) → Nontrivial W →
    ∀ φ : Y →* MulAut W, (∀ U : Subgroup W, (∀ y : Y, ∀ u ∈ U, φ y u ∈ U) → U = ⊥ ∨ U = ⊤) →
    ∀ T₀ V₀ : Subgroup Y, IsSylowTwoOf T₀ ⊤ → V₀ ≤ T₀ → (∀ s ∈ T₀, ∀ v ∈ V₀, s * v * s⁻¹ ∈ V₀) →
      (∀ v ∈ V₀, (fixV (Subgroup.zpowers (φ v))).index ≤ 2) → ∀ v ∈ V₀, φ v = 1

end CFSG.Quasithin
