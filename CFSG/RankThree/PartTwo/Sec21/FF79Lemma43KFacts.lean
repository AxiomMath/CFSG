module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

@[expose] def Is2El {M : Type*} [Monoid M] (x : M) : Prop := ∃ m : ℕ, x ^ (2 ^ m) = 1

@[expose] def FF79KO2L5 : Prop :=
  ∀ φ : MulAut (GL (Fin 5) (ZMod 2)), φ * φ = 1 → φ ≠ 1 →
    ∀ y₁ y₂ : GL (Fin 5) (ZMod 2), orderOf y₁ = 3 → orderOf y₂ = 3 → y₁ * y₂ = y₂ * y₁ →
      y₂ ∉ Subgroup.zpowers y₁ → φ y₁ = y₁ → φ y₂ = y₂ →
      ∀ r : MulAut (GL (Fin 5) (ZMod 2)), r * φ = φ * r → Is2El r → r ≠ 1 → r ≠ φ →
        ∃ c : GL (Fin 5) (ZMod 2), φ c = c ∧
          ¬ Is2El (MulAut.conj c * r * (MulAut.conj c)⁻¹ * r⁻¹)

@[expose] def FF79KAut5Fix : Prop :=
  ∀ y₁ y₂ : GL (Fin 5) (ZMod 2), orderOf y₁ = 3 → orderOf y₂ = 3 → y₁ * y₂ = y₂ * y₁ →
    y₂ ∉ Subgroup.zpowers y₁ →
    ∀ r r' : MulAut (GL (Fin 5) (ZMod 2)), r y₁ = y₁ → r y₂ = y₂ → r' y₁ = y₁ → r' y₂ = y₂ →
      Is2El r → Is2El r' → r ≠ 1 → r' ≠ 1 → r = r'

@[expose] def FF79KO2A5 : Prop :=
  ∀ φ : MulAut (alternatingGroup (Fin 5)), φ * φ = 1 →
    ∀ γ : alternatingGroup (Fin 5), orderOf γ = 3 → φ γ = γ →
      ∀ k : alternatingGroup (Fin 5), φ k = k → k ≠ 1 → Is2El k →
        ∃ c : alternatingGroup (Fin 5), φ c = c ∧ ¬ Is2El (c * k * c⁻¹ * k⁻¹)

@[expose] def FF79KO2L3 : Prop :=
  ∀ φ : MulAut (GL (Fin 3) (ZMod 2)), φ * φ = 1 →
    ∀ β : GL (Fin 3) (ZMod 2), orderOf β = 3 → φ β = β →
      ∀ k : GL (Fin 3) (ZMod 2), φ k = k → k ≠ 1 → Is2El k →
        ∃ c : GL (Fin 3) (ZMod 2), φ c = c ∧ ¬ Is2El (c * k * c⁻¹ * k⁻¹)

end CFSG.RankThree.PartTwo.Sec21.FF79
