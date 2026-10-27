module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

@[expose] def FF79KAutL5 : Prop :=
  ∀ φ : MulAut (GL (Fin 5) (ZMod 2)), φ * φ = 1 →
    ∀ y₁ y₂ ρ : GL (Fin 5) (ZMod 2), orderOf y₁ = 3 → orderOf y₂ = 3 → y₁ * y₂ = y₂ * y₁ →
      y₂ ∉ Subgroup.zpowers y₁ → orderOf ρ = 5 → ρ * (y₁ * y₂) = (y₁ * y₂) * ρ →
      φ y₁ = y₁ → φ y₂ = y₂ → φ ρ = ρ → φ = 1

@[expose] def FF79KTransvL5 : Prop :=
  ∀ s y z : GL (Fin 5) (ZMod 2), orderOf s = 2 → orderOf y = 3 →
    7 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set (GL (Fin 5) (ZMod 2)))) →
    s * y * s⁻¹ = y⁻¹ → orderOf z = 3 → z * y = y * z → z ∉ Subgroup.zpowers y → s * z = z * s →
    ∀ R : Subgroup (GL (Fin 5) (ZMod 2)), IsPGroup 2 R →
      R ≤ Subgroup.centralizer ({s} : Set (GL (Fin 5) (ZMod 2))) →
      (∀ g ∈ Subgroup.centralizer ({s} : Set (GL (Fin 5) (ZMod 2))), ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers s

@[expose] def FF79KCentL3 : Prop :=
  ∀ s y : GL (Fin 3) (ZMod 2), orderOf s = 2 → y * s = s * y → y ^ 2 = 1 ∨ y ^ 2 = s

@[expose] def FF79KCentA5 : Prop :=
  ∀ w g : alternatingGroup (Fin 5), orderOf w = 3 → g * w = w * g → g ∈ Subgroup.zpowers w

end CFSG.RankThree.PartTwo.Sec21.FF79
