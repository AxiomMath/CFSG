module

public import CFSG.Quasithin.Background.JonesParshallSector
public import CFSG.Quasithin.SteinbergCBI16Alt6
public import CFSG.Quasithin.SteinbergCBI16Alt7
public import CFSG.Quasithin.SteinbergCBI16Alt8
public import CFSG.Quasithin.SteinbergCBI16Orth4
public import CFSG.Quasithin.SteinbergCBI16Faithful
public import CFSG.Quasithin.SteinbergCBI16Proj

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open CFSG.Quasithin CFSG.Quasithin.JonesParshall

theorem natural_binary_module_first_cohomology.{u, v}
    :
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Finite Γ]
      [Finite W] (ρ : Representation (ZMod 2) Γ W),
        Finite (Z1 ρ) ∧ Finite (B1 ρ) ∧ Finite (H1 ρ)) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, Explicit.AlternatingNatural ρ 5 .alternating →
        Module.finrank (ZMod 2) (H1 ρ) = 0 ∧
          Module.Projective (MonoidAlgebra (ZMod 2) Γ) ρ.asModule) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, Explicit.AlternatingNatural ρ 6 .alternating →
        Module.finrank (ZMod 2) (H1 ρ) = 1) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, Explicit.AlternatingNatural ρ 7 .alternating →
        Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, Explicit.AlternatingNatural ρ 8 .alternating →
        Module.finrank (ZMod 2) (H1 ρ) = 1) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] {a : ℕ} {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ a → 1 < a → Explicit.BinaryNaturalSL ρ 2 F .natural →
        Module.finrank (ZMod 2) (H1 ρ) = a) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] [CharP F 2] {a : ℕ} {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ (2 * a) → 0 < a → Explicit.BinaryOrthogonalFour ρ F a →
        Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {F : Type} [Field F] [Fintype F] [CharP F 2] {ρ : Representation (ZMod 2) Γ W},
      Fintype.card F = 2 ^ (2 * 1) → Explicit.BinaryOrthogonalFour ρ F 1 →
        Explicit.AlternatingNatural ρ 5 .alternating ∧
          Module.Projective (MonoidAlgebra (ZMod 2) Γ) ρ.asModule) ∧
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
          Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W} {p : Fin 8} {ε : Explicit.NatDual}, Explicit.A7Four ρ p ε →
        Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, (Γ ≃* ↥(alternatingGroup (Fin 7))) →
        Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) W = 4 →
          Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W} {ε : Explicit.TripleTwist}, Explicit.TripleA6Six ρ ε →
        Module.finrank (ZMod 2) (H1 ρ) = 0) ∧
    (∀ {Γ : Type u} [Group Γ] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      {ρ : Representation (ZMod 2) Γ W}, Explicit.IsTripleCover Γ ↥(alternatingGroup (Fin 6)) →
        Function.Injective ρ → ρ.IsIrreducible → Module.finrank (ZMod 2) W = 6 →
          Module.finrank (ZMod 2) (H1 ρ) = 0) := by
  obtain ⟨j2, j3, j4, j5, j5', j6, j7⟩ := natural_binary_first_cohomology_sector.{u, v}
  refine ⟨fun ρ => ?_, fun h => ⟨finrank_H1_alternatingNatural_five h,
    projective_alternatingNatural_five h⟩, fun h => finrank_H1_alternatingNatural_six h,
    fun h => finrank_H1_alternatingNatural_seven h, fun h => finrank_H1_alternatingNatural_eight h,
    j2, j3, fun hF h => ⟨Orth4.alternatingNatural_of_binaryOrthogonalFour hF h,
      projective_alternatingNatural_five (Orth4.alternatingNatural_of_binaryOrthogonalFour hF h)⟩,
    j4, j5, j5', j6, j7, fun h => finrank_H1_a7Four h,
    fun θ hρ _ hdim => finrank_H1_faithful_alt7 θ hρ hdim, fun h => finrank_H1_tripleA6Six h,
    fun hP hρ hirr hdim => ?_⟩
  · have : Finite (Z1 ρ) := Subtype.finite
    exact ⟨this, Subtype.finite, Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)⟩
  · obtain ⟨-, ⟨e⟩, -⟩ := hP
    exact finrank_H1_faithful_center e hρ hirr (by omega)

end CFSG.Quasithin.SteinbergCB.I16
