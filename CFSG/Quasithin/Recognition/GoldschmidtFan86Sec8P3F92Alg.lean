module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

theorem zpow_eq_of_five {x : H} (hx : x ^ 5 = 1) (m n q : ℤ) (h : m = n + 5 * q) :
    x ^ m = x ^ n := by
  rw [h, zpow_add, zpow_mul, show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast, hx, one_zpow,
    mul_one]

theorem fcomm_eq_one_of_mul_comm {a b : H} (h : a * b = b * a) : fcomm a b = 1 := by
  unfold fcomm
  calc a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
    _ = 1 := by rw [h]; group

theorem mul_comm_of_fcomm_eq_one {a b : H} (h : fcomm a b = 1) : a * b = b * a := by
  unfold fcomm at h
  calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
    _ = b * a := by rw [h]; group

theorem conj_eq_of_fcomm_eq_one {a b : H} (h : fcomm a b = 1) : a⁻¹ * b * a = b := by
  have := mul_comm_of_fcomm_eq_one h
  calc a⁻¹ * b * a = a⁻¹ * (b * a) := by group
    _ = a⁻¹ * (a * b) := by rw [this]
    _ = b := by group

theorem conj_sq_eq_one {g u : H} (hu : u * u = 1) : (g⁻¹ * u * g) ^ 2 = 1 := by
  rw [pow_two]
  calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
    _ = 1 := by rw [hu]; group

theorem mul_mul_self_eq_one {a b : H} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha, hb]; group

theorem zpow_invol {z : H} (hz : z * z = 1) (n : ℤ) : z ^ n = 1 ∨ z ^ n = z := by
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hz, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hz, one_zpow, one_mul, zpow_one]

theorem Y_eq_conj {x : H} {Y : Fin 5 → H} (hY : ∀ j, x⁻¹ * Y j * x = Y (j + 1)) :
    Y 1 = x ^ (-1 : ℤ) * Y 0 * x ^ (1 : ℤ) ∧ Y 2 = x ^ (-2 : ℤ) * Y 0 * x ^ (2 : ℤ) ∧
      Y 3 = x ^ (-3 : ℤ) * Y 0 * x ^ (3 : ℤ) ∧ Y 4 = x ^ (-4 : ℤ) * Y 0 * x ^ (4 : ℤ) := by
  have hs : ∀ (k : ℤ) (u : H),
      x⁻¹ * (x ^ (-k) * u * x ^ k) * x = x ^ (-(k + 1)) * u * x ^ (k + 1) :=
    fun k u => by group
  have s1 : Y 1 = x⁻¹ * Y 0 * x := (hY 0).symm
  have s2 : Y 2 = x⁻¹ * Y 1 * x := (hY 1).symm
  have s3 : Y 3 = x⁻¹ * Y 2 * x := (hY 2).symm
  have s4 : Y 4 = x⁻¹ * Y 3 * x := (hY 3).symm
  have h1 : Y 1 = x ^ (-1 : ℤ) * Y 0 * x ^ (1 : ℤ) := by
    rw [s1]
    group
  have h2 : Y 2 = x ^ (-2 : ℤ) * Y 0 * x ^ (2 : ℤ) := by
    rw [s2, h1, hs 1]
    norm_num
  have h3 : Y 3 = x ^ (-3 : ℤ) * Y 0 * x ^ (3 : ℤ) := by
    rw [s3, h2, hs 2]
    norm_num
  have h4 : Y 4 = x ^ (-4 : ℤ) * Y 0 * x ^ (4 : ℤ) := by
    rw [s4, h3, hs 3]
    norm_num
  exact ⟨h1, h2, h3, h4⟩

theorem conj_tauLab {x w : H} {Y : Fin 5 → H} (hx : x ^ 5 = 1) (hw : w⁻¹ * x * w = x ^ 2)
    (hY : ∀ j, x⁻¹ * Y j * x = Y (j + 1)) (h2 : w⁻¹ * Y 2 * w = Y 2) (j : Fin 5) :
    w⁻¹ * Y j * w = Y (tauLab j) := by
  obtain ⟨e1, e2, e3, e4⟩ := Y_eq_conj hY
  have hwz : ∀ n : ℤ, w⁻¹ * x ^ n * w = x ^ (2 * n) := by
    intro n
    have h := conj_zpow (a := w⁻¹) (b := x) (i := n)
    rw [inv_inv] at h
    rw [← h, hw, ← zpow_natCast, ← zpow_mul]
    norm_num
  have hb : w⁻¹ * Y 0 * w = x ^ (2 : ℤ) * Y 0 * x ^ (-2 : ℤ) := by
    have h := h2
    rw [e2] at h
    have h' : x ^ (-4 : ℤ) * (w⁻¹ * Y 0 * w) * x ^ (4 : ℤ) =
        x ^ (-2 : ℤ) * Y 0 * x ^ (2 : ℤ) := by
      have a1 := hwz (-2)
      have a2 := hwz 2
      calc x ^ (-4 : ℤ) * (w⁻¹ * Y 0 * w) * x ^ (4 : ℤ)
          = (w⁻¹ * x ^ (-2 : ℤ) * w) * (w⁻¹ * Y 0 * w) * (w⁻¹ * x ^ (2 : ℤ) * w) := by
            rw [a1, a2]
            norm_num
        _ = w⁻¹ * (x ^ (-2 : ℤ) * Y 0 * x ^ (2 : ℤ)) * w := by group
        _ = _ := h
    calc w⁻¹ * Y 0 * w
        = x ^ (4 : ℤ) * (x ^ (-4 : ℤ) * (w⁻¹ * Y 0 * w) * x ^ (4 : ℤ)) * x ^ (-4 : ℤ) := by group
      _ = x ^ (4 : ℤ) * (x ^ (-2 : ℤ) * Y 0 * x ^ (2 : ℤ)) * x ^ (-4 : ℤ) := by rw [h']
      _ = x ^ (2 : ℤ) * Y 0 * x ^ (-2 : ℤ) := by group
  have key : ∀ k : ℤ, w⁻¹ * (x ^ (-k) * Y 0 * x ^ k) * w =
      x ^ (2 - 2 * k) * Y 0 * x ^ (2 * k - 2) := by
    intro k
    calc w⁻¹ * (x ^ (-k) * Y 0 * x ^ k) * w
        = (w⁻¹ * x ^ (-k) * w) * (w⁻¹ * Y 0 * w) * (w⁻¹ * x ^ k * w) := by group
      _ = x ^ (2 * -k) * (x ^ (2 : ℤ) * Y 0 * x ^ (-2 : ℤ)) * x ^ (2 * k) := by
        rw [hwz, hwz, hb]
      _ = x ^ (2 - 2 * k) * Y 0 * x ^ (2 * k - 2) := by group
  fin_cases j
  · show w⁻¹ * Y 0 * w = Y 3
    rw [hb, e3, zpow_eq_of_five hx (-3) 2 (-1) (by norm_num),
      zpow_eq_of_five hx 3 (-2) 1 (by norm_num)]
  · show w⁻¹ * Y 1 * w = Y 0
    rw [e1, key 1]
    norm_num
  · exact h2
  · show w⁻¹ * Y 3 * w = Y 4
    rw [e3, key 3, e4]
    norm_num
  · show w⁻¹ * Y 4 * w = Y 1
    rw [e4, key 4, e1, zpow_eq_of_five hx (2 - 2 * 4) (-1) (-1) (by norm_num),
      zpow_eq_of_five hx (2 * 4 - 2) 1 1 (by norm_num)]

end CFSG.Quasithin.Fan86
