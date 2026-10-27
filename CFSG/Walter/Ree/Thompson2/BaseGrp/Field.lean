module

public import CFSG.Walter.Ree.Thompson3.ThompsonAut

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

variable {k : Type} [Field k] [Fintype k] [CharP k 3] {σ : k ≃+* k} {n : ℕ}

omit [Field k] [CharP k 3] in
theorem card_mod_four (hk : Fintype.card k = 3 ^ (2 * n + 1)) : Fintype.card k % 4 = 3 := by
  rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

omit [CharP k 3] in
theorem not_isSquare_neg_one (hk : Fintype.card k = 3 ^ (2 * n + 1)) : ¬IsSquare (-1 : k) := by
  rw [FiniteField.isSquare_neg_one_iff, not_not]
  exact card_mod_four hk

omit [Fintype k] in
theorem ringChar_ne_two : ringChar k ≠ 2 := by
  rw [ringChar.eq k 3]
  norm_num

theorem isSquare_or_isSquare_neg (hk : Fintype.card k = 3 ^ (2 * n + 1)) (β : k) :
    IsSquare β ∨ IsSquare (-β) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · exact Or.inl ⟨0, by ring⟩
  have hq := card_mod_four hk
  set q := Fintype.card k with hqdef
  have hq2 : q / 2 = 2 * (q / 4) + 1 := by omega
  have hsq : (β ^ (q / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    have : q / 2 * 2 = q - 1 := by omega
    rw [this]
    exact FiniteField.pow_card_sub_one_eq_one β hβ
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact Or.inl ((FiniteField.isSquare_iff ringChar_ne_two hβ).mpr h)
  · right
    rw [FiniteField.isSquare_iff ringChar_ne_two (neg_ne_zero.mpr hβ), neg_pow, h, hq2,
      pow_succ, pow_mul]
    norm_num

theorem isSquare_sigma_mul (hk : Fintype.card k = 3 ^ (2 * n + 1)) (x : k) :
    IsSquare (σ x * x) := by
  obtain ⟨b, -, hb⟩ := Bombieri.exists_eq_frob_pow hk σ
  obtain ⟨c, hc⟩ : Odd (3 ^ b) := Odd.pow (by decide)
  refine ⟨x ^ (c + 1), ?_⟩
  rw [hb, ← pow_succ, hc, ← pow_add]
  ring_nf

theorem sigma_mul_eq_one (hk : Fintype.card k = 3 ^ (2 * n + 1)) {x : k} (hx : σ x * x = 1) :
    x = 1 ∨ x = -1 := by
  obtain ⟨b, -, hb⟩ := Bombieri.exists_eq_frob_pow hk σ
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hσx : σ x = x⁻¹ := eq_inv_of_mul_eq_one_left hx
  have hpar : ∀ j : ℕ, (σ ^ (2 * j + 1)) x = x⁻¹ := by
    intro j
    induction j with
    | zero => simpa using hσx
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, pow_succ', pow_succ',
        RingAut.mul_apply, RingAut.mul_apply, ih, map_inv₀, hσx, inv_inv, hσx]
  have hfix : (σ ^ (2 * n + 1)) x = x := by
    rw [Bombieri.pow_apply_of_eq_frob_pow hb, mul_comm, pow_mul, ← hk,
      FiniteField.pow_card_pow]
  rw [hpar n] at hfix
  have h2 : x ^ 2 = 1 := by
    rw [sq]
    calc x * x = x * x⁻¹ := by rw [hfix]
      _ = 1 := mul_inv_cancel₀ hx0
  exact sq_eq_one_iff.mp h2

theorem exists_sigma_mul_eq (hk : Fintype.card k = 3 ^ (2 * n + 1)) (hn : 1 ≤ n) {β : k}
    (hβ : IsSquare β) : ∃ κ : k, σ κ * κ = β := by
  obtain ⟨a, -, ha⟩ := exists_a_of_ker hk (odd_two_mul_add_one n) (by omega)
    (fun x hx => sigma_mul_eq_one hk hx)
  obtain ⟨μ, rfl⟩ := hβ
  refine ⟨μ ^ a, ?_⟩
  rw [map_pow, ← mul_pow, ha, sq]

end CFSG.Walter.Ree.T2.BaseGrp
