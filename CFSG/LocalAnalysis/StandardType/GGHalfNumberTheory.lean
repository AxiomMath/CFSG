module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private lemma card_F2 : Nat.card F2 = 2 := by
  change Nat.card (GaloisField 2 1) = 2
  rw [GaloisField.card 2 1 (by omega)]
  norm_num

private lemma card_gf4 : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by omega)]
  norm_num

private lemma succ_mul_div_two (k : ℕ) (hk : 1 ≤ k) :
    (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  have h : (k + 1) * k = k * (k - 1) + k * 2 := by
    have h1 : k + 1 = (k - 1) + 2 := by omega
    rw [Nat.mul_comm (k + 1) k, h1, Nat.mul_add]
  rw [h, Nat.add_mul_div_right (k * (k - 1)) k (by norm_num : (0:ℕ) < 2)]

private lemma four_pow_div_two (r : ℕ) :
    (4:ℕ) ^ (r * (r - 1) / 2) = 2 ^ (r * (r - 1)) := by
  rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
      Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self r)]

private lemma card_sl_two_succ_mul (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (SpecialLinearGroup (Fin (k + 1)) F2) =
      Nat.card (SpecialLinearGroup (Fin k) F2) * (2 ^ k * (2 ^ (k + 1) - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := k + 1) (by omega),
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := k) (by omega),
      card_F2]
  simp only [Nat.add_sub_cancel]
  rw [succ_mul_div_two k hk, pow_add]
  rw [Finset.prod_Icc_succ_top (a := 2) (b := k) (by omega) (fun j => 2 ^ j - 1)]
  ring

private lemma card_sl_two_lt_succ (k : ℕ) (hk : 1 ≤ k) :
    Nat.card (SpecialLinearGroup (Fin k) F2) <
      Nat.card (SpecialLinearGroup (Fin (k + 1)) F2) := by
  rw [card_sl_two_succ_mul k hk]
  have hfac : 1 < 2 ^ k * (2 ^ (k + 1) - 1) := by
    have h2 : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega : k ≠ 0) 2
    have h3 : 1 ≤ 2 ^ (k + 1) - 1 := by
      have : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega : k + 1 ≠ 0) 2
      omega
    have hm := Nat.mul_le_mul h2 h3
    omega
  calc Nat.card (SpecialLinearGroup (Fin k) F2)
      = Nat.card (SpecialLinearGroup (Fin k) F2) * 1 := (Nat.mul_one _).symm
    _ < Nat.card (SpecialLinearGroup (Fin k) F2) * (2 ^ k * (2 ^ (k + 1) - 1)) :=
        Nat.mul_lt_mul_of_pos_left hfac Nat.card_pos

theorem card_sl_two_strictMono {k l : ℕ} (hk : 2 ≤ k) (hkl : k < l) :
    Nat.card (SpecialLinearGroup (Fin k) F2) < Nat.card (SpecialLinearGroup (Fin l) F2) := by
  refine Nat.le_induction (m := k + 1)
    (P := fun l _ => Nat.card (SpecialLinearGroup (Fin k) F2) <
      Nat.card (SpecialLinearGroup (Fin l) F2)) ?_ ?_ l (by omega)
  · exact card_sl_two_lt_succ k (by omega)
  · intro n hn ih
    exact lt_trans ih (card_sl_two_lt_succ n (by omega))

private lemma card_sl_two_le_of_le {k m : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m) :
    Nat.card (SpecialLinearGroup (Fin k) F2) ≤
      Nat.card (SpecialLinearGroup (Fin m) F2) := by
  rcases eq_or_lt_of_le hkm with h | h
  · rw [h]
  · exact le_of_lt (card_sl_two_strictMono hk h)

private lemma pow_two_mul_odd_ne {a b O O' : ℕ} (hO : ¬ 2 ∣ O) (hO' : ¬ 2 ∣ O')
    (h : 2 ^ a * O = 2 ^ b * O') (hab : a < b) : False := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have hd : 1 ≤ d := by omega
  rw [pow_add, mul_assoc] at h
  have h2 : O = 2 ^ d * O' :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : (0:ℕ) < 2) a) h
  have h2d : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
  exact hO (by rw [h2]; exact h2d.mul_right O')

private lemma exp_lt_exp (r m : ℕ) (hr : 4 ≤ r) (hrm : 2 * r ≤ m + 2) :
    r * (r - 1) < m * (m - 1) / 2 := by
  have hm2 : 2 * r - 2 ≤ m := by omega
  have hm3 : 2 * r - 3 ≤ m - 1 := by omega
  have hle : (2 * r - 2) * (2 * r - 3) ≤ m * (m - 1) := Nat.mul_le_mul hm2 hm3
  have heq : (2 * r - 2) * (2 * r - 3) / 2 = (r - 1) * (2 * r - 3) := by
    have h2 : 2 * r - 2 = 2 * (r - 1) := by omega
    rw [h2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
  have hstrict : r * (r - 1) < (r - 1) * (2 * r - 3) := by
    have hgt : r < 2 * r - 3 := by omega
    have hpos : 0 < r - 1 := by omega
    have h := Nat.mul_lt_mul_of_pos_left hgt hpos
    rw [Nat.mul_comm (r - 1) r] at h
    exact h
  calc r * (r - 1) < (r - 1) * (2 * r - 3) := hstrict
    _ = (2 * r - 2) * (2 * r - 3) / 2 := heq.symm
    _ ≤ m * (m - 1) / 2 := Nat.div_le_div_right hle

theorem card_sl_four_ne_card_sl_two {r m : ℕ} (hr : 2 ≤ r) (hm : 4 ≤ m) (hrm : 2 * r ≤ m + 2) :
    Nat.card (SpecialLinearGroup (Fin r) (GaloisField 2 2)) ≠
      Nat.card (SpecialLinearGroup (Fin m) F2) := by
  intro heq
  have hg2 : Nat.card (SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = 60 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), card_gf4]
    norm_num
  have hg3 : Nat.card (SpecialLinearGroup (Fin 3) (GaloisField 2 2)) = 60480 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 3) (by norm_num), card_gf4]
    decide
  have hf4 : Nat.card (SpecialLinearGroup (Fin 4) F2) = 20160 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 4) (by norm_num), card_F2]
    decide
  have hf5 : Nat.card (SpecialLinearGroup (Fin 5) F2) = 9999360 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 5) (by norm_num), card_F2]
    decide
  rcases lt_or_ge r 4 with hr34 | hr4
  · interval_cases r
    ·
      have hle : Nat.card (SpecialLinearGroup (Fin 4) F2) ≤
          Nat.card (SpecialLinearGroup (Fin m) F2) :=
        card_sl_two_le_of_le (by norm_num : 2 ≤ 4) hm
      have hlt : (60:ℕ) < Nat.card (SpecialLinearGroup (Fin m) F2) := by
        have : (60:ℕ) < Nat.card (SpecialLinearGroup (Fin 4) F2) := by rw [hf4]; norm_num
        exact lt_of_lt_of_le this hle
      rw [hg2] at heq
      omega
    ·
      rcases eq_or_lt_of_le hm with hm4 | hm5
      · subst m
        rw [hg3, hf4] at heq
        omega
      · have hle : Nat.card (SpecialLinearGroup (Fin 5) F2) ≤
            Nat.card (SpecialLinearGroup (Fin m) F2) :=
          card_sl_two_le_of_le (by norm_num : 2 ≤ 5) (by omega)
        have hlt : Nat.card (SpecialLinearGroup (Fin 3) (GaloisField 2 2)) <
            Nat.card (SpecialLinearGroup (Fin m) F2) := by
          rw [hg3]
          calc (60480:ℕ) < 9999360 := by norm_num
            _ = Nat.card (SpecialLinearGroup (Fin 5) F2) := hf5.symm
            _ ≤ Nat.card (SpecialLinearGroup (Fin m) F2) := hle
        exact (ne_of_lt hlt) heq
  ·
    have hg : Nat.card (SpecialLinearGroup (Fin r) (GaloisField 2 2)) =
        2 ^ (r * (r - 1)) * (∏ j ∈ Finset.Icc 2 r, (4 ^ j - 1)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := r) (by omega), card_gf4]
      rw [four_pow_div_two r]
    have hf : Nat.card (SpecialLinearGroup (Fin m) F2) =
        2 ^ (m * (m - 1) / 2) * (∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := m) (by omega), card_F2]
    have hO : ¬ 2 ∣ (∏ j ∈ Finset.Icc 2 r, (4 ^ j - 1)) :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.not_dvd_prod_pow_sub_one
        Nat.prime_two (by norm_num : 2 ∣ 4) (by norm_num : 1 ≤ 4) r
    have hO' : ¬ 2 ∣ (∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1)) :=
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.not_dvd_prod_pow_sub_one
        Nat.prime_two (dvd_refl 2) (by norm_num : 1 ≤ 2) m
    have h : 2 ^ (r * (r - 1)) * (∏ j ∈ Finset.Icc 2 r, (4 ^ j - 1)) =
        2 ^ (m * (m - 1) / 2) * (∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1)) := by
      rw [← hg, ← hf]
      exact heq
    exact pow_two_mul_odd_ne hO hO' h (exp_lt_exp r m hr4 hrm)

end CFSG.StandardType.GGHalf

end
