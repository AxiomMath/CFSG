module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

/-!
# Class functions and the scalar product

Class functions `G → ℂ`, the scalar product `(φ, ψ)_G = |G|⁻¹ Σ φ(g) conj(ψ(g))`,
and the predicates character / irreducible character / generalized character /
linear character / disjointness.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.Theory.Character

universe u

/-- A class function `G → ℂ`. -/
public abbrev ClassFunction (G : Type u) := G → ℂ

/-- Constant on conjugacy classes. -/
@[expose] public def IsClassFunction {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∀ x g : G, φ (g * x * g⁻¹) = φ x

/-- The paper's inner product `(φ, ψ)_G = |G|⁻¹ Σ φ(g) conj(ψ(g))`. -/
@[expose] public def scalarProduct (G : Type u) [Fintype G] (φ ψ : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * star (ψ g)

/-- `|φ| = (φ, φ)`. -/
@[expose] public def normSq (G : Type u) [Fintype G] (φ : ClassFunction G) : ℂ :=
  scalarProduct G φ φ

/-- Supported on a set `A`. -/
@[expose] public def supportedOn {G : Type u} (φ : ClassFunction G) (A : Set G) : Prop :=
  ∀ g : G, g ∉ A → φ g = 0

/-- The characters of `G`. -/
@[expose] public def IsCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ), φ = ρ.character

/-- The irreducible characters of `G`. -/
@[expose] public def IsIrreducibleCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∃ n : ℕ, ∃ ρ : Representation ℂ G (Fin n → ℂ),
    Representation.IsIrreducible ρ ∧ φ = ρ.character

/-- A generalized character is a difference of two characters. -/
@[expose] public def IsGeneralizedCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  ∃ χ ψ : ClassFunction G, IsCharacter χ ∧ IsCharacter ψ ∧ φ = χ - ψ

/-- A linear (i.e. degree-one irreducible) character. -/
@[expose] public def IsLinearCharacter {G : Type u} [Group G] (φ : ClassFunction G) : Prop :=
  IsIrreducibleCharacter φ ∧ φ 1 = 1

/-- Two class functions are disjoint if no irreducible character occurs in both. -/
@[expose] public def Disjoint {G : Type u} [Group G] [Fintype G] (φ ψ : ClassFunction G) : Prop :=
  ∀ χ : ClassFunction G, IsIrreducibleCharacter χ →
    scalarProduct G χ φ ≠ 0 → scalarProduct G χ ψ = 0

/-! ## Basic algebra of the scalar product -/

section ScalarProduct

variable {G : Type u} [Fintype G]

public lemma scalarProduct_add_left (φ₁ φ₂ ψ : ClassFunction G) :
    scalarProduct G (φ₁ + φ₂) ψ = scalarProduct G φ₁ ψ + scalarProduct G φ₂ ψ := by
  calc
    scalarProduct G (φ₁ + φ₂) ψ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x + φ₂ x) * star (ψ x) := by
      rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x * star (ψ x) + φ₂ x * star (ψ x)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [add_mul]
    _ = (Nat.card G : ℂ)⁻¹ * (∑ x : G, φ₁ x * star (ψ x) + ∑ x : G, φ₂ x * star (ψ x)) := by
      rw [Finset.sum_add_distrib]
    _ = scalarProduct G φ₁ ψ + scalarProduct G φ₂ ψ := by
      rw [mul_add]
      rfl

public lemma scalarProduct_smul_left (z : ℂ) (φ ψ : ClassFunction G) :
    scalarProduct G (z • φ) ψ = z * scalarProduct G φ ψ := by
  calc
    scalarProduct G (z • φ) ψ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, z * (φ g * star (ψ g)) := by
      simp [scalarProduct, mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (z * ∑ g : G, φ g * star (ψ g)) := by
      rw [← Finset.mul_sum]
    _ = z * scalarProduct G φ ψ := by
      simp [scalarProduct, mul_left_comm]

public lemma scalarProduct_add_right (φ ψ₁ ψ₂ : ClassFunction G) :
    scalarProduct G φ (ψ₁ + ψ₂) = scalarProduct G φ ψ₁ + scalarProduct G φ ψ₂ := by
  calc
    scalarProduct G φ (ψ₁ + ψ₂) = (Nat.card G : ℂ)⁻¹ * ∑ x : G, φ x * star (ψ₁ x + ψ₂ x) := by
      rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ x * star (ψ₁ x) + φ x * star (ψ₂ x)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      calc
        φ x * star (ψ₁ x + ψ₂ x) = φ x * (star (ψ₁ x) + star (ψ₂ x)) := by
          congr 1
          exact map_add (starRingEnd ℂ) (ψ₁ x) (ψ₂ x)
        _ = φ x * star (ψ₁ x) + φ x * star (ψ₂ x) := by rw [mul_add]
    _ = (Nat.card G : ℂ)⁻¹ * (∑ x : G, φ x * star (ψ₁ x) + ∑ x : G, φ x * star (ψ₂ x)) := by
      rw [Finset.sum_add_distrib]
    _ = scalarProduct G φ ψ₁ + scalarProduct G φ ψ₂ := by
      rw [mul_add]
      rfl

public lemma scalarProduct_smul_right (z : ℂ) (φ ψ : ClassFunction G) :
    scalarProduct G φ (z • ψ) = scalarProduct G φ ψ * star z := by
  calc
    scalarProduct G φ (z • ψ)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, (φ g * star (ψ g)) * star z := by
            unfold scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card G : ℂ)⁻¹ * ((∑ g : G, φ g * star (ψ g)) * star z) := by
          rw [Finset.sum_mul]
    _ = scalarProduct G φ ψ * star z := by
          simp [scalarProduct, mul_left_comm, mul_comm]

public lemma scalarProduct_sub_left (φ₁ φ₂ ψ : ClassFunction G) :
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
  calc
    scalarProduct G (φ₁ - φ₂) ψ = scalarProduct G (φ₁ + (-1 : ℂ) • φ₂) ψ := by
      simp [sub_eq_add_neg]
    _ = scalarProduct G φ₁ ψ + (-1 : ℂ) * scalarProduct G φ₂ ψ := by
      rw [scalarProduct_add_left, scalarProduct_smul_left]
    _ = scalarProduct G φ₁ ψ - scalarProduct G φ₂ ψ := by
      ring

public lemma scalarProduct_conj (φ ψ : ClassFunction G) :
    star (scalarProduct G φ ψ) = scalarProduct G ψ φ := by
  unfold scalarProduct
  calc
    star ((Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * star (ψ g))
        = star ((Nat.card G : ℂ)⁻¹) * star (∑ g : G, φ g * star (ψ g)) := by
          simp
    _ = (Nat.card G : ℂ)⁻¹ * (∑ g : G, star (φ g * star (ψ g))) := by
          simp
    _ = (Nat.card G : ℂ)⁻¹ * (∑ g : G, star (φ g) * ψ g) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro g hg
          calc
            star (φ g * star (ψ g)) = star (φ g) * star (star (ψ g)) := by
              exact map_mul (starRingEnd ℂ) (φ g) (star (ψ g))
            _ = star (φ g) * ψ g := by simp
    _ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ψ g * star (φ g) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro g hg
          ring

public lemma scalarProduct_self_real (φ : ClassFunction G) :
    star (scalarProduct G φ φ) = scalarProduct G φ φ := by
  simp [scalarProduct_conj]

variable [Group G]

/-- The `g⁻¹`-form product; agrees with `scalarProduct` on characters. -/
@[expose] public def characterProduct (G : Type u) [Group G] [Fintype G] (φ ψ : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, φ g * ψ g⁻¹

public lemma characterProduct_add_left (φ₁ φ₂ ψ : ClassFunction G) :
    characterProduct G (φ₁ + φ₂) ψ = characterProduct G φ₁ ψ + characterProduct G φ₂ ψ := by
  calc
    characterProduct G (φ₁ + φ₂) ψ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x + φ₂ x) * ψ x⁻¹ := by
      rfl
    _ = (Nat.card G : ℂ)⁻¹ * ∑ x : G, (φ₁ x * ψ x⁻¹ + φ₂ x * ψ x⁻¹) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [add_mul]
    _ = (Nat.card G : ℂ)⁻¹ * (∑ x : G, φ₁ x * ψ x⁻¹ + ∑ x : G, φ₂ x * ψ x⁻¹) := by
      rw [Finset.sum_add_distrib]
    _ = characterProduct G φ₁ ψ + characterProduct G φ₂ ψ := by
      rw [mul_add]
      rfl

public lemma characterProduct_smul_left (z : ℂ) (φ ψ : ClassFunction G) :
    characterProduct G (z • φ) ψ = z * characterProduct G φ ψ := by
  calc
    characterProduct G (z • φ) ψ = (Nat.card G : ℂ)⁻¹ * ∑ g : G, z * (φ g * ψ g⁻¹) := by
      simp [characterProduct, mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (z * ∑ g : G, φ g * ψ g⁻¹) := by
      rw [← Finset.mul_sum]
    _ = z * characterProduct G φ ψ := by
      simp [characterProduct, mul_left_comm]

end ScalarProduct

end CFSG.Theory.Character
