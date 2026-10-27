module

public import CFSG.Quasithin.Background.JonesParshallSLn
public import CFSG.Quasithin.Background.JonesParshallSp4Derived
public import CFSG.Quasithin.Background.JonesParshallG2Field
public import CFSG.Quasithin.Background.JonesParshallSL5Wedge

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

theorem jonesParshall_values.{u, v}
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
      {ρ : Representation (ZMod 2) Γ W}, Explicit.SL5ExteriorTwo ρ →
        Module.finrank (ZMod 2) (H1 ρ) = 0) := by
  refine ⟨fun hF ha h => ?_, fun hF ha h => finrank_H1_orthogonalFour hF ha h,
    fun hF ha h => ?_, fun hF ha h => finrank_H1_sp4Derived hF ha h,
    fun hF ha h => finrank_H1_G2Derived hF ha h, fun hd hF h => finrank_H1_SL45 hd hF h,
    fun h => finrank_H1_SL5ExteriorTwo h⟩
  · have : CharP _ 2 := charP_of_card_eq_prime_pow hF
    exact finrank_H1_SL2 hF ha h
  · have : CharP _ 2 := charP_of_card_eq_prime_pow hF
    exact finrank_H1_SL3 hF ha h

end CFSG.Quasithin.JonesParshall
