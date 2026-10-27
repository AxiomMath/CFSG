module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {K : Type} [Field K]
  [Algebra (ZMod 2) K]

structure IsG2Model (H : Subgroup (GLV V))
    (G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) (φ : ↥H ≃* ↥G₀)
    (π : quasithinZorn K →ₗ[ZMod 2] V) : Prop where
  surj : ∀ v : V, ∃ x : quasithinZorn K, x.1 + x.2.2.2 = 0 ∧ π x = v
  ker : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → (π x = 0 ↔ ∃ c : K, x = (c, 0, 0, c))
  equiv : ∀ (h : ↥H) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 →
    π (((φ h : ↥G₀) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x) = (h : GLV V) (π x)

theorem isG2NaturalModule_iff {H : Subgroup (GLV V)}
    {G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)} :
    IsG2NaturalModule H G₀ ↔ ∃ (φ : ↥H ≃* ↥G₀) (π : quasithinZorn K →ₗ[ZMod 2] V),
      IsG2Model H G₀ φ π :=
  ⟨fun ⟨φ, π, h1, h2, h3⟩ => ⟨φ, π, ⟨h1, h2, h3⟩⟩,
    fun ⟨φ, π, ⟨h1, h2, h3⟩⟩ => ⟨φ, π, h1, h2, h3⟩⟩

end CFSG.Quasithin.G11.SzG11S.Two
