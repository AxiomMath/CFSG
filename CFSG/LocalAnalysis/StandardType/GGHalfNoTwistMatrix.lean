module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.StandardType.GGHalf

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 3)

@[expose] def ntN₁ : Mat3 := !![1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def ntN₂ : Mat3 := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def ntP (i j a b : ZMod 3) : Mat3 := !![i, a, 0; j, b, 0; 0, 0, 1]

@[expose] def ntPinv (i j a b : ZMod 3) : Mat3 :=
  !![(i * b - j * a)⁻¹ * b, -((i * b - j * a)⁻¹ * a), 0;
     -((i * b - j * a)⁻¹ * j), (i * b - j * a)⁻¹ * i, 0; 0, 0, 1]

private lemma zmod3_cases (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = 2 := by
  revert z; decide

private lemma nt_shear_witness (i j a b : ZMod 3) (hj : j ≠ 0) (hD : i * b - j * a ≠ 0)
    (hnt : i ≠ 0 ∨ b ≠ 0) :
    (∃ A F : Fin 3 → ZMod 3, A ≠ 0 ∧ F ≠ 0 ∧ F ⬝ᵥ A = 0 ∧
      ntN₁ * (ntP i j a b * ntN₁ * ntPinv i j a b) = 1 + Matrix.vecMulVec A F) ∨
    (∃ A F : Fin 3 → ZMod 3, A ≠ 0 ∧ F ≠ 0 ∧ F ⬝ᵥ A = 0 ∧
      (ntN₁ * (ntP i j a b * ntN₁ * ntPinv i j a b)) ^ 2 = 1 + Matrix.vecMulVec A F) ∨
    (∃ A F : Fin 3 → ZMod 3, A ≠ 0 ∧ F ≠ 0 ∧ F ⬝ᵥ A = 0 ∧
      (ntN₂ * (ntP i j a b * ntN₂ * ntPinv i j a b)) ^ 2 = 1 + Matrix.vecMulVec A F) := by
  rcases zmod3_cases i with rfl | rfl | rfl <;>
    rcases zmod3_cases j with rfl | rfl | rfl <;>
    rcases zmod3_cases a with rfl | rfl | rfl <;>
    rcases zmod3_cases b with rfl | rfl | rfl <;>
    (first | (exfalso; revert hj hD hnt; decide) | decide +kernel)

theorem ntP_mul_ntPinv (i j a b : ZMod 3) (hD : i * b - j * a ≠ 0) :
    ntP i j a b * ntPinv i j a b = 1 := by
  revert i j a b
  decide +kernel

theorem exists_shear (i j a b : ZMod 3) (hj : j ≠ 0) (hD : i * b - j * a ≠ 0)
    (hnt : i ≠ 0 ∨ b ≠ 0) :
    ∃ w ∈ Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
        ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3),
      ∃ A F : Fin 3 → ZMod 3, A ≠ 0 ∧ F ≠ 0 ∧ F ⬝ᵥ A = 0 ∧ w = 1 + Matrix.vecMulVec A F := by
  have hN1 : ntN₁ ∈ Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) :=
    Submonoid.subset_closure (by simp)
  have hN2 : ntN₂ ∈ Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) :=
    Submonoid.subset_closure (by simp)
  have hSK : ntP i j a b * ntN₁ * ntPinv i j a b ∈
      Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) :=
    Submonoid.subset_closure (by simp)
  have hH : ntP i j a b * ntN₂ * ntPinv i j a b ∈
      Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) :=
    Submonoid.subset_closure (by simp)
  have hW1 : ntN₁ * (ntP i j a b * ntN₁ * ntPinv i j a b) ∈
      Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) := mul_mem hN1 hSK
  have hW2 : (ntN₁ * (ntP i j a b * ntN₁ * ntPinv i j a b)) ^ 2 ∈
      Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) := pow_mem hW1 2
  have hNH : ntN₂ * (ntP i j a b * ntN₂ * ntPinv i j a b) ∈
      Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) := mul_mem hN2 hH
  have hW3 : (ntN₂ * (ntP i j a b * ntN₂ * ntPinv i j a b)) ^ 2 ∈
      Submonoid.closure ({ntN₁, ntN₂, ntP i j a b * ntN₁ * ntPinv i j a b,
      ntP i j a b * ntN₂ * ntPinv i j a b} : Set Mat3) := pow_mem hNH 2
  rcases nt_shear_witness i j a b hj hD hnt with ⟨A, F, hA, hF, hdot, hw⟩ |
      ⟨A, F, hA, hF, hdot, hw⟩ | ⟨A, F, hA, hF, hdot, hw⟩
  · exact ⟨_, hW1, A, F, hA, hF, hdot, hw⟩
  · exact ⟨_, hW2, A, F, hA, hF, hdot, hw⟩
  · exact ⟨_, hW3, A, F, hA, hF, hdot, hw⟩

end CFSG.StandardType.GGHalf

end
