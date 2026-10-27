module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

@[expose] def FF79KTransvComm : Prop :=
  ∀ s y z : GL (Fin 5) (ZMod 2), orderOf s = 2 → orderOf y = 3 →
    7 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set (GL (Fin 5) (ZMod 2)))) →
    s * y * s⁻¹ = y⁻¹ → orderOf z = 3 → z * y = y * z → z ∉ Subgroup.zpowers y → s * z = z * s →
    ∀ d : GL (Fin 5) (ZMod 2), (∃ n : ℕ, d ^ (2 ^ n) = 1) → d * s = s * d → d * z = z * d →
    ∀ R : Subgroup (GL (Fin 5) (ZMod 2)), IsPGroup 2 R →
      R ≤ Subgroup.centralizer ({s} : Set (GL (Fin 5) (ZMod 2))) →
      (∀ g ∈ Subgroup.centralizer ({s} : Set (GL (Fin 5) (ZMod 2))), ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      ∀ r ∈ R, d * r * d⁻¹ * r⁻¹ ∈ Subgroup.zpowers s

@[expose] def FF79KTransvCenter : Prop :=
  ∀ s y z : GL (Fin 5) (ZMod 2), orderOf s = 2 → orderOf y = 3 →
    7 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set (GL (Fin 5) (ZMod 2)))) →
    s * y * s⁻¹ = y⁻¹ → orderOf z = 3 → z * y = y * z → z ∉ Subgroup.zpowers y → s * z = z * s →
    ∀ R : Subgroup (GL (Fin 5) (ZMod 2)), IsPGroup 2 R →
      R ≤ Subgroup.centralizer ({s} : Set (GL (Fin 5) (ZMod 2))) →
      (∀ g ∈ Subgroup.centralizer ({s} : Set (GL (Fin 5) (ZMod 2))), ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ ≠ r₂ * r₁ →
      ∀ r ∈ R, (∀ x ∈ R, r * x = x * r) → r ∈ Subgroup.zpowers s

@[expose] def FF79KCentL3NonAb : Prop :=
  ∀ s : GL (Fin 3) (ZMod 2), orderOf s = 2 → ∃ d₁ d₂ : GL (Fin 3) (ZMod 2),
    d₁ * s = s * d₁ ∧ d₂ * s = s * d₂ ∧ d₁ ^ 4 = 1 ∧ d₂ ^ 4 = 1 ∧ d₁ * d₂ ≠ d₂ * d₁

end CFSG.RankThree.PartTwo.Sec21.FF79
