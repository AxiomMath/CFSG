module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.Quasithin.SBd19F

section Dihedral

variable {E : Type*} [Group E] {u₁ u₂ : E}

private theorem dihedral_cube_mul (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (h4 : (u₁ * u₂) ^ 4 = 1) :
    (u₁ * u₂) ^ 3 * u₁ = u₂ := by
  have h3 : (u₁ * u₂) ^ 3 * (u₁ * u₂) = 1 := by rw [← pow_succ]; exact h4
  rw [eq_inv_of_mul_eq_one_left h3, mul_inv_rev, inv_eq_of_mul_eq_one_right h1,
    inv_eq_of_mul_eq_one_right h2, mul_assoc, h1, mul_one]

private theorem dihedral_conj (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (h4 : (u₁ * u₂) ^ 4 = 1)
    (j : ℕ) :
    u₁ * (u₁ * u₂) ^ j = (u₁ * u₂) ^ (3 * j) * u₁ := by
  have h31 := dihedral_cube_mul h1 h2 h4
  have h11 : u₁ * (u₁ * u₂) = u₂ := by rw [← mul_assoc, h1, one_mul]
  induction j with
  | zero => simp
  | succ j ih =>
    calc u₁ * (u₁ * u₂) ^ (j + 1) = (u₁ * (u₁ * u₂) ^ j) * (u₁ * u₂) := by rw [pow_succ, mul_assoc]
      _ = (u₁ * u₂) ^ (3 * j) * (u₁ * (u₁ * u₂)) := by rw [ih, mul_assoc]
      _ = (u₁ * u₂) ^ (3 * j) * u₂ := by rw [h11]
      _ = (u₁ * u₂) ^ (3 * (j + 1)) * u₁ := by
        rw [show 3 * (j + 1) = 3 * j + 3 by omega, pow_add, mul_assoc, h31]

private theorem dihedral_weak_form (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (h4 : (u₁ * u₂) ^ 4 = 1)
    {x : E} (hx : x ∈ Subgroup.closure ({u₁, u₂} : Set E)) :
    ∃ i e : ℕ, e < 2 ∧ x = (u₁ * u₂) ^ i * u₁ ^ e := by
  have hc := dihedral_conj h1 h2 h4
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨0, 1, by decide, by simp⟩
    · exact ⟨3, 1, by decide, by simpa using (dihedral_cube_mul h1 h2 h4).symm⟩
  | one => exact ⟨0, 0, by decide, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, e, he, rfl⟩ := hx
    obtain ⟨j, d, hd, rfl⟩ := hy
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;>
      rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · exact ⟨i + j, 0, by decide, by simp [pow_add]⟩
    · exact ⟨i + j, 1, by decide, by simp [pow_add, mul_assoc]⟩
    · refine ⟨i + 3 * j, 1, by decide, ?_⟩
      simp only [pow_one, pow_zero, mul_one, pow_add]
      rw [mul_assoc, hc, mul_assoc]
    · refine ⟨i + 3 * j, 0, by decide, ?_⟩
      simp only [pow_one, pow_zero, mul_one, pow_add]
      have : u₁ * ((u₁ * u₂) ^ j * u₁) = (u₁ * u₂) ^ (3 * j) := by
        rw [← mul_assoc, hc, mul_assoc, h1, mul_one]
      rw [mul_assoc, this]
  | inv x _ hx =>
    obtain ⟨i, e, he, rfl⟩ := hx
    have hinv : ((u₁ * u₂) ^ i)⁻¹ = (u₁ * u₂) ^ (3 * i) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show i + 3 * i = 4 * i by omega, pow_mul, h4, one_pow]
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · exact ⟨3 * i, 0, by decide, by simpa using hinv⟩
    · refine ⟨9 * i, 1, by decide, ?_⟩
      rw [pow_one, mul_inv_rev, inv_eq_of_mul_eq_one_right h1, hinv, hc,
        show 3 * (3 * i) = 9 * i by omega]

theorem exists_dihedral_form (h1 : u₁ * u₁ = 1) (h2 : u₂ * u₂ = 1) (h4 : (u₁ * u₂) ^ 4 = 1)
    {x : E} (hx : x ∈ Subgroup.closure ({u₁, u₂} : Set E)) :
    ∃ i e : ℕ, i < 4 ∧ e < 2 ∧ x = (u₁ * u₂) ^ i * u₁ ^ e := by
  obtain ⟨i, e, he, rfl⟩ := dihedral_weak_form h1 h2 h4 hx
  exact ⟨i % 4, e, Nat.mod_lt _ (by decide), he, by rw [← pow_eq_pow_mod i h4]⟩

end Dihedral

end CFSG.Quasithin.SBd19F
