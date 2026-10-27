module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.L3Aut.Bor

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

theorem x12_zero : x12 (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x23_zero : x23 (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem torus_one : (torus 1 : SpecialLinearGroup (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x12_mul (s t : K) : x12 s * x12 t = x12 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem x23_mul (s t : K) : x23 s * x23 t = x23 (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem torus_mul (a b : Kˣ) :
    (torus a : SpecialLinearGroup (Fin 3) K) * torus b = torus (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

theorem x12_inv (t : K) : (x12 t)⁻¹ = x12 (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [x12_mul, add_neg_cancel, x12_zero])

theorem x23_inv (t : K) : (x23 t)⁻¹ = x23 (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [x23_mul, add_neg_cancel, x23_zero])

theorem torus_pow (a : Kˣ) (m : ℕ) :
    (torus a : SpecialLinearGroup (Fin 3) K) ^ m = torus (a ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, torus_one]
  | succ m ih => rw [pow_succ, ih, torus_mul, pow_succ]

theorem x12_mul_torus_mul_inv (a : Kˣ) (s : K) :
    x12 s * torus a * (x12 s)⁻¹ = torus a * x12 (s * (1 - (a : K)) / a) := by
  have ha : (a : K) ≠ 0 := a.ne_zero
  rw [x12_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp
  all_goals ring

theorem x23_mul_torus_mul_inv (a : Kˣ) (s : K) :
    x23 s * torus a * (x23 s)⁻¹ = torus a * x23 (s * (((a⁻¹ : Kˣ) : K) - 1)) := by
  have ha : (a : K) ≠ 0 := a.ne_zero
  rw [x23_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp
  all_goals ring

theorem x12_eq_torus_inv_mul (a : Kˣ) (ha : a ≠ 1) (t : K) :
    x12 t = (torus a)⁻¹ * (x12 (t * a / (1 - (a : K))) * torus a *
      (x12 (t * a / (1 - (a : K))))⁻¹) := by
  have h0 : (a : K) ≠ 0 := a.ne_zero
  have h1 : (1 : K) - a ≠ 0 := sub_ne_zero.mpr fun h => ha (Units.val_eq_one.mp h.symm)
  rw [x12_mul_torus_mul_inv, inv_mul_cancel_left]
  congr 1
  field_simp

theorem x23_eq_torus_inv_mul (a : Kˣ) (ha : a ≠ 1) (t : K) :
    x23 t = (torus a)⁻¹ * (x23 (t / (((a⁻¹ : Kˣ) : K) - 1)) * torus a *
      (x23 (t / (((a⁻¹ : Kˣ) : K) - 1)))⁻¹) := by
  have h1 : ((a⁻¹ : Kˣ) : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => ha (inv_eq_one.mp (Units.val_eq_one.mp h))
  rw [x23_mul_torus_mul_inv, inv_mul_cancel_left]
  congr 1
  field_simp

theorem x12_mem_upperTriangular (t : K) : x12 t ∈ upperTriangular 3 K := by
  rw [mem_upperTriangular]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp

theorem x23_mem_upperTriangular (t : K) : x23 t ∈ upperTriangular 3 K := by
  rw [mem_upperTriangular]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp

theorem torus_mem_upperTriangular (a : Kˣ) : (torus a : SpecialLinearGroup (Fin 3) K) ∈
    upperTriangular 3 K := by
  rw [mem_upperTriangular]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp

theorem odd_card_units [Finite K] [CharP K 2] : Odd (Nat.card Kˣ) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  rw [Nat.card_units, hK]
  exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' n.ne_zero).mpr even_two) odd_one

theorem odd_orderOf_proj_torus [Finite K] [CharP K 2] (a : Kˣ) :
    Odd (orderOf (proj 3 K (torus a))) := by
  have h1 : (proj 3 K (torus a)) ^ Nat.card Kˣ = 1 := by
    rw [← map_pow, torus_pow, pow_card_eq_one', torus_one, map_one]
  exact odd_card_units.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

theorem orderOf_proj_conj (g h : SpecialLinearGroup (Fin 3) K) :
    orderOf (proj 3 K (g * h * g⁻¹)) = orderOf (proj 3 K h) := by
  have : proj 3 K (g * h * g⁻¹) = MulAut.conj (proj 3 K g) (proj 3 K h) := by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  rw [this, MulEquiv.orderOf_eq]

theorem fixed_torus_inv_mul_conj [Finite K] [CharP K 2] {β : MulAut (projectiveSL 3 K)}
    (hβ : ∀ z ∈ projUpperTriangular 3 K, Odd (orderOf z) → β z = z) (a : Kˣ)
    {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ upperTriangular 3 K) :
    β (proj 3 K ((torus a)⁻¹ * (g * torus a * g⁻¹))) =
      proj 3 K ((torus a)⁻¹ * (g * torus a * g⁻¹)) := by
  have ht : (torus a : SpecialLinearGroup (Fin 3) K) ∈ upperTriangular 3 K :=
    torus_mem_upperTriangular a
  have h1 : β (proj 3 K (torus a)⁻¹) = proj 3 K (torus a)⁻¹ :=
    hβ _ (Subgroup.mem_map_of_mem (proj 3 K) ((upperTriangular 3 K).inv_mem ht))
      (by rw [map_inv, orderOf_inv]; exact odd_orderOf_proj_torus a)
  have h2 : β (proj 3 K (g * torus a * g⁻¹)) = proj 3 K (g * torus a * g⁻¹) :=
    hβ _ (Subgroup.mem_map_of_mem (proj 3 K)
      ((upperTriangular 3 K).mul_mem ((upperTriangular 3 K).mul_mem hg ht)
        ((upperTriangular 3 K).inv_mem hg)))
      (by rw [orderOf_proj_conj]; exact odd_orderOf_proj_torus a)
  rw [map_mul (proj 3 K), map_mul β, h1, h2]

theorem fixed_x12 [Finite K] [CharP K 2] {β : MulAut (projectiveSL 3 K)}
    (hβ : ∀ z ∈ projUpperTriangular 3 K, Odd (orderOf z) → β z = z) {a : Kˣ} (ha : a ≠ 1)
    (t : K) : β (proj 3 K (x12 t)) = proj 3 K (x12 t) := by
  have := fixed_torus_inv_mul_conj hβ a (x12_mem_upperTriangular (t * a / (1 - (a : K))))
  rwa [← x12_eq_torus_inv_mul a ha t] at this

theorem fixed_x23 [Finite K] [CharP K 2] {β : MulAut (projectiveSL 3 K)}
    (hβ : ∀ z ∈ projUpperTriangular 3 K, Odd (orderOf z) → β z = z) {a : Kˣ} (ha : a ≠ 1)
    (t : K) : β (proj 3 K (x23 t)) = proj 3 K (x23 t) := by
  have := fixed_torus_inv_mul_conj hβ a
    (x23_mem_upperTriangular (t / (((a⁻¹ : Kˣ) : K) - 1)))
  rwa [← x23_eq_torus_inv_mul a ha t] at this

theorem exists_fixed_of_fixes_odd {K : Type*} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (β : MulAut (projectiveSL 3 K))
    (hβ : ∀ z ∈ projUpperTriangular 3 K, Odd (orderOf z) → β z = z) :
    ∃ a : Kˣ, a ≠ 1 ∧
      (∀ t : K, β (proj 3 K (CFSG.Quasithin.L3Aut.x12 t)) =
        proj 3 K (CFSG.Quasithin.L3Aut.x12 t)) ∧
      β (proj 3 K (CFSG.Quasithin.L3Aut.x23 1)) = proj 3 K (CFSG.Quasithin.L3Aut.x23 1) ∧
      β (proj 3 K (CFSG.Quasithin.L3Aut.torus a)) =
        proj 3 K (CFSG.Quasithin.L3Aut.torus a) := by
  have hcard : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
  exact ⟨a, ha, fixed_x12 hβ ha, fixed_x23 hβ ha 1,
    hβ _ (Subgroup.mem_map_of_mem (proj 3 K) (torus_mem_upperTriangular a))
      (odd_orderOf_proj_torus a)⟩

end CFSG.Quasithin.L3Aut.Bor
