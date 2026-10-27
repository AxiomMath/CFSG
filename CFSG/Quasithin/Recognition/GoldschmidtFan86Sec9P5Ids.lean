module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Coll
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres2
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

structure P5Ids (w za : H) (y z : Fin 5 → H) (xb t w2 ub : H) (zm ym za' : Fin 3 → H)
    (e₁ e₂ : ℕ) : Prop where
  e1le : e₁ ≤ 1
  e2le : e₂ ≤ 1
  t_eq : t = y 0
  xb3 : xb ^ 3 = 1
  xb_t : t⁻¹ * xb * t = xb⁻¹
  zm0 : zm 0 = z 0
  zm1 : zm 1 = t⁻¹ * zm 2 * t
  zm2 : zm 2 = w * w * za
  za0 : za' 0 = za
  za1 : za' 1 = z 2 * za
  za2 : za' 2 = z 2
  ym0 : ym 0 = z 0 * z 1
  ym1 : ym 1 = ym 0 * ym 2
  ym2 : ym 2 = y 2 * za' 2
  ub_eq : ub = z 1 * z 3 * za
  w2_eq : w2 = y 3 * y 4 * z 3 * z 2 ^ e₁ * za ^ e₂
  xz : ∀ i, xb⁻¹ * zm i * xb = zm (i + 1)
  xy : ∀ i, xb⁻¹ * ym i * xb = ym (i + 1)
  xa : ∀ i, xb⁻¹ * za' i * xb = za' (i + 1)
  xub : xb⁻¹ * ub * xb = ub
  xw : xb⁻¹ * w * xb = w2

theorem fin3_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem fin3_forall_ne {P : Fin 3 → Fin 3 → Prop} (h01 : P 0 1) (h02 : P 0 2) (h10 : P 1 0)
    (h12 : P 1 2) (h20 : P 2 0) (h21 : P 2 1) : ∀ i j, i ≠ j → P i j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01
  · exact h02
  · exact h10
  · exact absurd rfl hij
  · exact h12
  · exact h20
  · exact h21
  · exact absurd rfl hij

theorem fin3_forall2 {P : Fin 3 → Fin 3 → Prop} (h00 : P 0 0) (h01 : P 0 1) (h02 : P 0 2)
    (h10 : P 1 0) (h11 : P 1 1) (h12 : P 1 2) (h20 : P 2 0) (h21 : P 2 1) (h22 : P 2 2) :
    ∀ i j, P i j := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h02, h10, h11, h12, h20, h21, h22]

theorem swap12_zero : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide

theorem swap12_one : Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide

theorem swap12_two : Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide

theorem fin3_neg_add_01 : -((0 : Fin 3) + 1) = 2 := by decide

theorem fin3_neg_add_02 : -((0 : Fin 3) + 2) = 1 := by decide

theorem fin3_neg_add_10 : -((1 : Fin 3) + 0) = 2 := by decide

theorem fin3_neg_add_12 : -((1 : Fin 3) + 2) = 0 := by decide

theorem fin3_neg_add_20 : -((2 : Fin 3) + 0) = 1 := by decide

theorem fin3_neg_add_21 : -((2 : Fin 3) + 1) = 0 := by decide

macro "idc " h:term:max hR:term:max : tactic =>
  `(tactic| (simp only [($h).t_eq, ($h).zm0, ($h).zm1, ($h).zm2, ($h).za0, ($h).za1, ($h).za2,
      ($h).ym0, ($h).ym1, ($h).ym2, ($h).ub_eq, swap12_zero, swap12_one, swap12_two,
      fin3_neg_add_01, fin3_neg_add_02, fin3_neg_add_10, fin3_neg_add_12, fin3_neg_add_20,
      fin3_neg_add_21]; try coll $hR))

macro "idcc " h:term:max hR:term:max hC:term:max hwc:term:max : tactic =>
  `(tactic| (simp only [($h).t_eq, ($h).zm0, ($h).zm1, ($h).zm2, ($h).za0, ($h).za1, ($h).za2,
      ($h).ym0, ($h).ym1, ($h).ym2, ($h).ub_eq, swap12_zero, swap12_one, swap12_two,
      fin3_neg_add_01, fin3_neg_add_02, fin3_neg_add_10, fin3_neg_add_12, fin3_neg_add_20,
      fin3_neg_add_21]; try collc $hR $hC $hwc))

macro "idcw " h:term:max hR:term:max : tactic =>
  `(tactic| (rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ($h).e1le with h1 | h1 <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ($h).e2le with h2 | h2 <;>
      simp only [($h).w2_eq, h1, h2] <;> idc $h $hR))

theorem conj_dual {xb t : H} (h : t⁻¹ * xb * t = xb⁻¹) (a : H) :
    xb⁻¹ * (t⁻¹ * (xb⁻¹ * a * xb) * t) * xb = t⁻¹ * a * t := by
  have h1 : xb * t * xb = t := by
    calc xb * t * xb = t * (t⁻¹ * xb * t) * xb := by group
      _ = t := by rw [h]; group
  have h2 : xb⁻¹ * t⁻¹ * xb⁻¹ = t⁻¹ := by
    have := congrArg (·⁻¹) h1
    simpa [mul_assoc] using this
  calc xb⁻¹ * (t⁻¹ * (xb⁻¹ * a * xb) * t) * xb
      = (xb⁻¹ * t⁻¹ * xb⁻¹) * a * (xb * t * xb) := by group
    _ = t⁻¹ * a * t := by rw [h1, h2]

theorem fcomm_eq_one_iff {a b : H} : fcomm a b = 1 ↔ b * a = a * b := by
  have : fcomm a b = (b * a)⁻¹ * (a * b) := by
    unfold fcomm
    group
  rw [this, inv_mul_eq_one]

theorem conj_mul' (x a b : H) : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group

end CFSG.Quasithin.Fan86
