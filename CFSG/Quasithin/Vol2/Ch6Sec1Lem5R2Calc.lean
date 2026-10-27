module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.R2

open scoped commutatorElement

variable {P : Type} [Group P]

theorem mul_eq_comm_mul (g h : P) : h * g = ⁅h, g⁆ * g * h := by
  rw [commutatorElement_def]; group

theorem pow_mul_eq_of_central {g h : P} (hc : ∀ k : P, ⁅h, g⁆ * k = k * ⁅h, g⁆) (n : ℕ) :
    h ^ n * g = ⁅h, g⁆ ^ n * g * h ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc' : h * ⁅h, g⁆ ^ n = ⁅h, g⁆ ^ n * h := ((Commute.pow_left (hc h) n).eq).symm
    calc h ^ (n + 1) * g = h * (h ^ n * g) := by rw [pow_succ', mul_assoc]
      _ = h * (⁅h, g⁆ ^ n * g * h ^ n) := by rw [ih]
      _ = (h * ⁅h, g⁆ ^ n) * (g * h ^ n) := by simp only [mul_assoc]
      _ = (⁅h, g⁆ ^ n * h) * (g * h ^ n) := by rw [hc']
      _ = ⁅h, g⁆ ^ n * (h * g) * h ^ n := by simp only [mul_assoc]
      _ = ⁅h, g⁆ ^ n * (⁅h, g⁆ * g * h) * h ^ n := by rw [mul_eq_comm_mul g h]
      _ = ⁅h, g⁆ ^ (n + 1) * g * h ^ (n + 1) := by
        rw [pow_succ, pow_succ']; simp only [mul_assoc]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  have := Nat.choose_succ_succ n 1
  simpa using this

theorem mul_pow_of_central {g h : P} (hc : ∀ k : P, ⁅h, g⁆ * k = k * ⁅h, g⁆) (n : ℕ) :
    (g * h) ^ n = g ^ n * h ^ n * ⁅h, g⁆ ^ n.choose 2 := by
  have hcomm : ∀ (m : ℕ) (k : P), ⁅h, g⁆ ^ m * k = k * ⁅h, g⁆ ^ m := fun m k =>
    (Commute.pow_left (hc k) m).eq
  induction n with
  | zero => simp
  | succ n ih =>
    calc (g * h) ^ (n + 1) = (g * h) ^ n * (g * h) := pow_succ _ _
      _ = g ^ n * h ^ n * ⁅h, g⁆ ^ n.choose 2 * (g * h) := by rw [ih]
      _ = g ^ n * (h ^ n * g) * h * ⁅h, g⁆ ^ n.choose 2 := by
        rw [mul_assoc (g ^ n * h ^ n) (⁅h, g⁆ ^ n.choose 2), hcomm _ (g * h)]
        simp only [mul_assoc]
      _ = g ^ n * (⁅h, g⁆ ^ n * g * h ^ n) * h * ⁅h, g⁆ ^ n.choose 2 := by
        rw [pow_mul_eq_of_central hc]
      _ = ⁅h, g⁆ ^ n * (g ^ n * g) * (h ^ n * h) * ⁅h, g⁆ ^ n.choose 2 := by
        rw [show g ^ n * (⁅h, g⁆ ^ n * g * h ^ n) = ⁅h, g⁆ ^ n * (g ^ n * g * h ^ n) by
          rw [← mul_assoc, ← mul_assoc, ← hcomm n (g ^ n)]; simp only [mul_assoc]]
        simp only [mul_assoc]
      _ = (g ^ n * g) * (h ^ n * h) * (⁅h, g⁆ ^ n * ⁅h, g⁆ ^ n.choose 2) := by
        rw [mul_assoc (⁅h, g⁆ ^ n) (g ^ n * g) (h ^ n * h), hcomm n ((g ^ n * g) * (h ^ n * h))]
        simp only [mul_assoc]
      _ = g ^ (n + 1) * h ^ (n + 1) * ⁅h, g⁆ ^ (n + 1).choose 2 := by
        rw [← pow_succ, ← pow_succ, ← pow_add, choose_two_succ]

theorem mul_pow_three_of_central {g h : P} (hc : ∀ k : P, ⁅h, g⁆ * k = k * ⁅h, g⁆)
    (h3 : ⁅h, g⁆ ^ 3 = 1) : (g * h) ^ 3 = g ^ 3 * h ^ 3 := by
  rw [mul_pow_of_central hc 3]
  norm_num [Nat.choose, h3]

theorem comm_mul_right_of_central {c : P} (hc : ∀ g k : P, ⁅c, g⁆ * k = k * ⁅c, g⁆) (g h : P) :
    ⁅c, g * h⁆ = ⁅c, g⁆ * ⁅c, h⁆ := by
  have e : ⁅c, g * h⁆ = ⁅c, g⁆ * (g * ⁅c, h⁆ * g⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, ← hc h g, mul_inv_cancel_right]

@[expose] def commHom (c : P) (hc : ∀ g k : P, ⁅c, g⁆ * k = k * ⁅c, g⁆) : P →* P where
  toFun g := ⁅c, g⁆
  map_one' := by simp
  map_mul' := comm_mul_right_of_central hc

theorem commHom_apply (c : P) (hc : ∀ g k : P, ⁅c, g⁆ * k = k * ⁅c, g⁆) (g : P) :
    commHom c hc g = ⁅c, g⁆ := rfl

theorem comm_pow_right_of_central {c : P} (hc : ∀ g k : P, ⁅c, g⁆ * k = k * ⁅c, g⁆) (g : P)
    (n : ℕ) : ⁅c, g ^ n⁆ = ⁅c, g⁆ ^ n := by
  have := map_pow (commHom c hc) g n
  simpa [commHom_apply] using this

theorem comm_swap (g c : P) : ⁅g, c⁆ = ⁅c, g⁆⁻¹ := by
  simp only [commutatorElement_def]; group

theorem comm_inv_left_of_central {c g : P} (hc : ∀ k : P, ⁅c, g⁆ * k = k * ⁅c, g⁆) :
    ⁅c⁻¹, g⁆ = ⁅c, g⁆⁻¹ := by
  have e : ⁅c⁻¹, g⁆ = c⁻¹ * ⁅c, g⁆⁻¹ * c := by
    simp only [commutatorElement_def]; group
  have h1 : ⁅c, g⁆⁻¹ * c = c * ⁅c, g⁆⁻¹ := by
    have h2 := hc c
    have h3 : (⁅c, g⁆ * c)⁻¹ = (c * ⁅c, g⁆)⁻¹ := by rw [h2]
    simp only [mul_inv_rev] at h3
    calc ⁅c, g⁆⁻¹ * c = c * (c⁻¹ * ⁅c, g⁆⁻¹) * c := by group
      _ = c * (⁅c, g⁆⁻¹ * c⁻¹) * c := by rw [h3]
      _ = c * ⁅c, g⁆⁻¹ := by group
  rw [e, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]

theorem comm_central_mul_left {w c g : P} (hw : ∀ k : P, w * k = k * w) :
    ⁅w * c, g⁆ = ⁅c, g⁆ := by
  simp only [commutatorElement_def]
  calc w * c * g * (w * c)⁻¹ * g⁻¹ = w * (c * g * c⁻¹) * w⁻¹ * g⁻¹ := by group
    _ = c * g * c⁻¹ * g⁻¹ := by rw [hw (c * g * c⁻¹), mul_inv_cancel_right]

theorem comm_mul_central_right {w c g : P} (hw : ∀ k : P, w * k = k * w) :
    ⁅c, g * w⁆ = ⁅c, g⁆ := by
  simp only [commutatorElement_def]
  calc c * (g * w) * c⁻¹ * (g * w)⁻¹ = c * g * (w * c⁻¹) * w⁻¹ * g⁻¹ := by group
    _ = c * g * c⁻¹ * g⁻¹ := by rw [hw c⁻¹]; group

theorem comm_of_closure_pair {x y : P} (hcl : Subgroup.closure {x, y} = ⊤) (hxy : x * y = y * x) :
    ∀ g k : P, g * k = k * g := by
  have hc : ∀ z : P, z = x ∨ z = y → ∀ g : P, g * z = z * g := by
    have hle : ∀ z : P, z = x ∨ z = y → Subgroup.closure {x, y} ≤
        Subgroup.centralizer ({z} : Set P) := by
      rintro z hz
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl) <;>
        rcases hz with rfl | rfl <;>
        simp [Subgroup.mem_centralizer_iff, hxy]
    intro z hz g
    have hg := hle z hz (hcl ▸ Subgroup.mem_top g)
    rw [Subgroup.mem_centralizer_iff] at hg
    exact (hg z rfl).symm
  have hcen : Subgroup.closure {x, y} ≤ Subgroup.center P := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_center_iff.mpr (hc _ (Or.inl rfl))
    · exact Subgroup.mem_center_iff.mpr (hc _ (Or.inr rfl))
  intro g k
  exact (Subgroup.mem_center_iff.mp (hcen (hcl ▸ Subgroup.mem_top k)) g)

theorem comm_pow_left_of_central {x y : P} (hc : ∀ k : P, ⁅x, y⁆ * k = k * ⁅x, y⁆) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ⁅x ^ (n + 1), y⁆ = x * ⁅x ^ n, y⁆ * x⁻¹ * ⁅x, y⁆ := by
      rw [pow_succ']; simp only [commutatorElement_def]; group
    rw [e, ih, ← (Commute.pow_left (hc x) n).eq, mul_inv_cancel_right, pow_succ]

theorem three_dvd_choose_two {n : ℕ} (hn : 1 ≤ n) : 3 ∣ (3 ^ n).choose 2 := by
  have h2 : (3 ^ n).choose 2 * 2 = 3 ^ n * (3 ^ n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd
  have h3 : 3 ∣ (3 ^ n).choose 2 * 2 := by
    rw [h2]
    exact dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
  exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime 3 2) h3)

end CFSG.Quasithin.H13.R2
