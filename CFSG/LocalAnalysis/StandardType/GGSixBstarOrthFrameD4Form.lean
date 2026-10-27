module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.StandardType

namespace OrthD4

open Matrix

theorem sq_eq_ite (a : ZMod 3) : a ^ 2 = if a ≠ 0 then 1 else 0 := by
  revert a
  decide

theorem sum_sq_eq_card {r : ℕ} (s : Fin r → ZMod 3) :
    ∑ i, s i ^ 2 = ((Finset.univ.filter fun i => s i ≠ 0).card : ZMod 3) := by
  simp_rw [sq_eq_ite]
  rw [Finset.sum_boole]

theorem sum_sq_eq_one_iff (s : Fin 4 → ZMod 3) :
    ∑ i, s i ^ 2 = 1 ↔
      (Finset.univ.filter fun i => s i ≠ 0).card = 1 ∨
        (Finset.univ.filter fun i => s i ≠ 0).card = 4 := by
  rw [sum_sq_eq_card]
  have hle : (Finset.univ.filter fun i => s i ≠ 0).card ≤ 4 :=
    (Finset.card_filter_le _ _).trans (by simp)
  generalize (Finset.univ.filter fun i => s i ≠ 0).card = k at hle ⊢
  interval_cases k <;> decide

theorem sum_sq_eq_dot {r : ℕ} (x : Fin r → ZMod 3) : ∑ i, x i ^ 2 = x ⬝ᵥ x := by
  simp [dotProduct, sq]

theorem dot_add_self {r : ℕ} (x y : Fin r → ZMod 3) :
    (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + y ⬝ᵥ y + 2 * (x ⬝ᵥ y) := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x]
  ring

theorem dot_sub_self {r : ℕ} (x y : Fin r → ZMod 3) :
    (x - y) ⬝ᵥ (x - y) = x ⬝ᵥ x + y ⬝ᵥ y - 2 * (x ⬝ᵥ y) := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm y x]
  ring

theorem eq_zero_of_ne_one {b : ZMod 3} (h1 : 1 + 1 + 2 * b ≠ 1) (h2 : 1 + 1 - 2 * b ≠ 1) :
    b = 0 := by
  revert b
  decide

theorem sum_sq_map_eq (F : (Fin 4 → ZMod 3) → (Fin 4 → ZMod 3))
    (hadd : ∀ x y, F (x + y) = F x + F y)
    (hF : ∀ x, ∑ i, F x i ^ 2 = 1 ↔ ∑ i, x i ^ 2 = 1) (x : Fin 4 → ZMod 3) :
    ∑ i, F x i ^ 2 = ∑ i, x i ^ 2 := by
  classical
  set Φ := (AddMonoidHom.mk' F hadd).toZModLinearMap 3 with hΦ
  have hΦF : ∀ y, Φ y = F y := fun y => rfl
  set e : Fin 4 → (Fin 4 → ZMod 3) := fun i => Pi.single i 1 with he
  set a : Fin 4 → (Fin 4 → ZMod 3) := fun i => F (e i) with ha
  have hee : ∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [he]
    · simp [he, hij, Ne.symm hij]
  have hQa : ∀ i, a i ⬝ᵥ a i = 1 := by
    intro i
    rw [← sum_sq_eq_dot, ha, hF, sum_sq_eq_dot, hee, ite_eq_left rfl]
  have hab : ∀ i j, i ≠ j → a i ⬝ᵥ a j = 0 := by
    intro i j hij
    have hp : F (e i + e j) = a i + a j := by rw [← hΦF, map_add, hΦF, hΦF]
    have hm : F (e i - e j) = a i - a j := by rw [← hΦF, map_sub, hΦF, hΦF]
    have h1 : ¬ (∑ k, F (e i + e j) k ^ 2 = 1) := by
      rw [hF, sum_sq_eq_dot, dot_add_self, hee, hee, hee, ite_eq_left rfl, ite_eq_left rfl,
        ite_eq_right hij]
      decide
    have h2 : ¬ (∑ k, F (e i - e j) k ^ 2 = 1) := by
      rw [hF, sum_sq_eq_dot, dot_sub_self, hee, hee, hee, ite_eq_left rfl, ite_eq_left rfl,
        ite_eq_right hij]
      decide
    rw [hp, sum_sq_eq_dot, dot_add_self, hQa, hQa] at h1
    rw [hm, sum_sq_eq_dot, dot_sub_self, hQa, hQa] at h2
    exact eq_zero_of_ne_one h1 h2
  have hdot : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hQa]
    · rw [ite_eq_right hij, hab i j hij]
  have hFx : F x = ∑ i, x i • a i := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [← hΦF, map_sum]
    simp only [map_smul]
    rfl
  rw [sum_sq_eq_dot, sum_sq_eq_dot, hFx, sum_dotProduct]
  simp only [dotProduct_sum, smul_dotProduct, dotProduct_smul, hdot, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [dotProduct]

end OrthD4

end CFSG.StandardType
