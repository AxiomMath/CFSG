module

public import CFSG.Quasithin.Background.JonesParshallSupport
public import CFSG.Quasithin.Background.JonesParshallCurtisClassify

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

theorem natural_binary_first_cohomology_sector.{u, v}
    :
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] {a : ℕ} {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ a → 1 < a → Explicit.BinaryNaturalSL ρ 2 F .natural →
        Module.finrank (ZMod 2) (H1 ρ) = a) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] [CharP F 2] {a : ℕ} {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ (2 * a) → 0 < a → Explicit.BinaryOrthogonalFour ρ F a →
        Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] {a : ℕ} {ε : Explicit.NatDual}
      {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ a → 0 < a → Explicit.BinaryNaturalSL ρ 3 F ε →
        Module.finrank (ZMod 2) (H1 ρ) = if a = 1 then 1 else 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] {a : ℕ} {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ a → 0 < a → Explicit.BinaryNaturalSp4Derived ρ F →
        Module.finrank (ZMod 2) (H1 ρ) = a) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] {a : ℕ} {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ a → 0 < a → Explicit.G2Natural ρ F .derived →
        Module.finrank (ZMod 2) (H1 ρ) = a) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] {d : ℕ} {ε : Explicit.NatDual}
      {ρ : Representation (ZMod 2) Γ W},
      (d = 4 ∨ d = 5) → Fintype.card F = 2 → Explicit.BinaryNaturalSL ρ d F ε →
        Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, (Γ ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
        ρ.IsIrreducible → Module.finrank (ZMod 2) W = 10 →
          Module.finrank (ZMod 2) (H1 ρ) = 0) := by
  obtain ⟨h1, h2, h3, h4, h4', h5, -⟩ := jonesParshall_values.{u, v}
  exact ⟨h1, h2, h3, h4, h4', h5, fun θ hρ hdim => Curtis.finrank_H1_irreducible_ten θ hρ hdim⟩

end CFSG.Quasithin.JonesParshall
