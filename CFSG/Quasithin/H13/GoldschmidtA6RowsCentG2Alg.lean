module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsCode
public import Mathlib.RingTheory.PiTensorProduct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin.H13.A6.GR

variable {d : ℕ}

theorem add_self_matrix (X : Matrix (Fin d) (Fin d) (ZMod 2)) : X + X = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem isUnit_sub_one_of_span {K : Matrix (Fin d) (Fin d) (ZMod 2)} (h : Span [K]) :
    IsUnit (K - 1) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  intro a b hab
  have hab' : a ᵥ* (K - 1) = b ᵥ* (K - 1) := hab
  have h0 : (a - b) ᵥ* (K - 1) = 0 := by rw [Matrix.sub_vecMul, hab', sub_self]
  by_contra hne
  obtain ⟨q, hq, y, hy⟩ := h (a - b) (sub_ne_zero.mpr hne)
  rw [List.mem_singleton] at hq
  subst hq
  apply hy
  have h1 : (a - b) ⬝ᵥ ((q - 1) *ᵥ y) = 0 := by
    rw [Matrix.dotProduct_mulVec, h0, zero_dotProduct]
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, sub_eq_zero] at h1

theorem sq_add_add_one {K : Matrix (Fin d) (Fin d) (ZMod 2)} (h3 : K ^ 3 = 1)
    (hu : IsUnit (K - 1)) : K * K + K + 1 = 0 := by
  have h : (K - 1) * (K * K + K + 1) = 0 := by
    have : (K - 1) * (K * K + K + 1) = K ^ 3 - 1 := by noncomm_ring
    rw [this, h3, sub_self]
  exact hu.mul_right_eq_zero.mp h

theorem eq_of_three {A B : Matrix (Fin d) (Fin d) (ZMod 2)} (hAB : A * B = B * A)
    (hA : A * A + A + 1 = 0) (hB : B * B + B + 1 = 0)
    (hC : A * B * (A * B) + A * B + 1 = 0) : A = B := by
  have hneg : ∀ X : Matrix (Fin d) (Fin d) (ZMod 2), -X = X := fun X =>
    neg_eq_iff_add_eq_zero.mpr (add_self_matrix X)
  have e1 : A * A = A + 1 := by
    have h : A * A + (A + 1) = 0 := by rw [← add_assoc]; exact hA
    rw [eq_neg_of_add_eq_zero_left h, hneg]
  have e2 : B * B = B + 1 := by
    have h : B * B + (B + 1) = 0 := by rw [← add_assoc]; exact hB
    rw [eq_neg_of_add_eq_zero_left h, hneg]
  have e3 : A * B * (A * B) = A * A * (B * B) := by
    calc A * B * (A * B) = A * (B * A) * B := by noncomm_ring
      _ = A * (A * B) * B := by rw [← hAB]
      _ = A * A * (B * B) := by noncomm_ring
  rw [e3, e1, e2] at hC
  have e4 : (A + 1) * (B + 1) + A * B + 1 =
      (A * B + A * B) + (1 + 1) + (A + B) := by noncomm_ring
  rw [e4, add_self_matrix, add_self_matrix, zero_add, zero_add] at hC
  rw [eq_neg_of_add_eq_zero_left hC, hneg]

theorem eq_of_fpf_three {A B : Matrix (Fin d) (Fin d) (ZMod 2)} (hAB : A * B = B * A)
    (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1) (hC3 : (A * B) ^ 3 = 1) (hA : IsUnit (A - 1))
    (hB : IsUnit (B - 1)) (hC : IsUnit (A * B - 1)) : A = B :=
  eq_of_three hAB (sq_add_add_one hA3 hA) (sq_add_add_one hB3 hB) (sq_add_add_one hC3 hC)

theorem exists_three_squared {Q : Type*} [Group Q] (hQ : Nat.card Q = 9) (h3 : ∀ q : Q, q ^ 3 = 1) :
    ∃ x y : Q, x * y = y * x ∧ x ≠ 1 ∧ y ≠ 1 ∧ x * y ≠ 1 ∧ x ≠ y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hQ]; norm_num)).is_comm.comm
      a b
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  obtain ⟨y, hy⟩ : ∃ y : Q, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.zpowers x = ⊤ := eq_top_iff.mpr fun y _ => hcon y
    have hc : Nat.card (Subgroup.zpowers x) = 9 := by rw [htop, Subgroup.card_top, hQ]
    rw [Nat.card_zpowers] at hc
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (h3 x))
    omega
  refine ⟨x, y, hcomm x y, hx, ?_, ?_, ?_⟩
  · rintro rfl
    exact hy (Subgroup.one_mem _)
  · intro h
    apply hy
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  · rintro rfl
    exact hy (Subgroup.mem_zpowers _)

theorem false_of_fpf_nine {Q : Type*} [Group Q] (hQ : Nat.card Q = 9) (h3 : ∀ q : Q, q ^ 3 = 1)
    (ρ : Q →* Matrix (Fin d) (Fin d) (ZMod 2)) (hρ : ∀ q, ρ q = 1 → q = 1)
    (hu : ∀ q, q ≠ 1 → IsUnit (ρ q - 1)) : False := by
  obtain ⟨x, y, hxy, hx, hy, hxy1, hne⟩ := exists_three_squared hQ h3
  have hcube : ∀ q : Q, ρ q ^ 3 = 1 := fun q => by rw [← map_pow, h3 q, map_one]
  have hA := eq_of_fpf_three (A := ρ x) (B := ρ y) (by rw [← map_mul, ← map_mul, hxy])
    (hcube x) (hcube y) (by rw [← map_mul]; exact hcube _) (hu x hx) (hu y hy)
    (by rw [← map_mul]; exact hu _ hxy1)
  apply hne
  have : ρ (x * y⁻¹) = 1 := by rw [map_mul, hA, ← map_mul, mul_inv_cancel, map_one]
  exact mul_inv_eq_one.mp (hρ _ this)

end CFSG.Quasithin.H13.A6.GR
