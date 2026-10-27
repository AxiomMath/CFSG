module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcShift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcDefs

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem nfw_append (r l : H) (e : ℤ) (K K' : List ℤ) :
    nfw r l e (K ++ K') = nfw r l e K * nfw r l (if Even K.length then e else -e) K' := by
  induction K generalizing e with
  | nil => simp [nfw]
  | cons t K ih =>
    simp only [List.cons_append, nfw, ih, mul_assoc, List.length_cons, Nat.even_add_one]
    by_cases hK : Even K.length <;> simp [hK]

theorem nfw_pair_neg (r l : H) (a b : ℤ) (K : List ℤ) :
    nfw r l (-1) (a :: b :: K) = (tx r l a)⁻¹ * (tx r l b * nfw r l (-1) K) := by
  simp [nfw]

theorem nfw_pair_pos (r l : H) (a b : ℤ) (K : List ℤ) :
    nfw r l 1 (a :: b :: K) = tx r l a * ((tx r l b)⁻¹ * nfw r l 1 K) := by
  simp [nfw]

theorem nfw_shift_r (r l : H) (j : ℤ) :
    ∀ K : List ℤ, Even K.length →
      r ^ (-j) * nfw r l (-1) K * r ^ j = nfw r l (-1) (K.map (· + j)) := by
  intro K
  induction K using List.twoStepInduction with
  | nil => intro _; simp [nfw]
  | singleton a => intro h; exact absurd h (by simp)
  | cons_cons a b K ih _ =>
    intro h
    have hK : Even K.length := by simpa [Nat.even_add_one, Nat.even_add] using h
    have e1 : r ^ (-j) * ((tx r l a)⁻¹ * (tx r l b * nfw r l (-1) K)) * r ^ j =
        (r ^ (-j) * ((tx r l a)⁻¹ * tx r l b) * r ^ j) * (r ^ (-j) * nfw r l (-1) K * r ^ j) := by
      group
    rw [nfw_pair_neg, e1, tx_shift, ih hK, List.map_cons, List.map_cons, nfw_pair_neg, mul_assoc]

theorem nfw_shift_l (r l : H) (j : ℤ) :
    ∀ K : List ℤ, Even K.length →
      l ^ (-j) * nfw r l 1 K * l ^ j = nfw r l 1 (K.map (· + j)) := by
  intro K
  induction K using List.twoStepInduction with
  | nil => intro _; simp [nfw]
  | singleton a => intro h; exact absurd h (by simp)
  | cons_cons a b K ih _ =>
    intro h
    have hK : Even K.length := by simpa [Nat.even_add_one, Nat.even_add] using h
    have e1 : l ^ (-j) * (tx r l a * ((tx r l b)⁻¹ * nfw r l 1 K)) * l ^ j =
        (l ^ (-j) * (tx r l a * (tx r l b)⁻¹) * l ^ j) * (l ^ (-j) * nfw r l 1 K * l ^ j) := by
      group
    rw [nfw_pair_pos, e1, tx_shift_l, ih hK, List.map_cons, List.map_cons, nfw_pair_pos, mul_assoc]

theorem xi_zpow_conj (hξ : ξ * ξ = 1) (g : H) (n : ℤ) : ξ * g ^ n * ξ = (ξ * g * ξ) ^ n := by
  have hinv : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ
  have := map_zpow (MulAut.conj ξ) g n
  simpa only [MulAut.conj_apply, hinv] using this

theorem xi_mul_conj (hξ : ξ * ξ = 1) (A B : H) : ξ * (A * B) * ξ = (ξ * A * ξ) * (ξ * B * ξ) := by
  calc ξ * (A * B) * ξ = ξ * A * (ξ * ξ) * B * ξ := by rw [hξ]; group
    _ = (ξ * A * ξ) * (ξ * B * ξ) := by group

theorem xi_tx_7 (h : IsTutteSys s r l ξ Hs) (h7 : ξ * r * ξ = r⁻¹ ∧ ξ * l * ξ = l⁻¹) (a : ℤ) :
    ξ * tx r l a * ξ = tx r l (-a) := by
  unfold tx
  rw [xi_mul_conj h.xi_sq, xi_zpow_conj h.xi_sq, xi_zpow_conj h.xi_sq, h7.1, h7.2]
  simp [inv_zpow']

theorem xi_tx_8 (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹) (a : ℤ) :
    ξ * tx r l a * ξ = (tx r l (-a))⁻¹ := by
  unfold tx
  rw [xi_mul_conj h.xi_sq, xi_zpow_conj h.xi_sq, xi_zpow_conj h.xi_sq, h8.1, h8.2]
  simp [inv_zpow']

end CFSG.Quasithin.Fan86.Tutte
