module

public import Certificates.Data.NPL587
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.NPLSound

open CFSG.Quasithin.H13.NPL

theorem dig_zero_eq (c : ℕ) : dig c 0 = c % 8 := by
  simp [dig]

theorem dig_succ_eq (c i : ℕ) : dig c (i + 1) = dig (c / 8) i := by
  unfold dig
  rw [pow_succ', ← Nat.div_div_eq_div_mul]

theorem dig_add8_zero (d e : ℕ) (hd : d < 8) : dig (d + 8 * e) 0 = d := by
  rw [dig_zero_eq]
  omega

theorem dig_add8_succ (d e i : ℕ) (hd : d < 8) : dig (d + 8 * e) (i + 1) = dig e i := by
  rw [dig_succ_eq, show (d + 8 * e) / 8 = e by omega]

theorem dig_small (d : ℕ) (hd : d < 8) : dig d 0 = d := by
  rw [dig_zero_eq]
  omega

theorem enc8_eq (d0 d1 d2 d3 d4 d5 d6 d7 : ℕ) :
    enc8 d0 d1 d2 d3 d4 d5 d6 d7
      = d0 + 8 * (d1 + 8 * (d2 + 8 * (d3 + 8 * (d4 + 8 * (d5 + 8 * (d6 + 8 * d7)))))) := by
  unfold enc8
  ring

theorem dig_enc8 (d0 d1 d2 d3 d4 d5 d6 d7 : ℕ) (h0 : d0 < 8) (h1 : d1 < 8) (h2 : d2 < 8)
    (h3 : d3 < 8) (h4 : d4 < 8) (h5 : d5 < 8) (h6 : d6 < 8) (h7 : d7 < 8) :
    dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 0 = d0 ∧ dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 1 = d1 ∧
      dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 2 = d2 ∧ dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 3 = d3 ∧
      dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 4 = d4 ∧ dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 5 = d5 ∧
      dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 6 = d6 ∧ dig (enc8 d0 d1 d2 d3 d4 d5 d6 d7) 7 = d7 := by
  simp only [enc8_eq, dig_add8_zero, dig_add8_succ, dig_small, h0, h1, h2, h3, h4, h5, h6, h7,
    and_self, true_and]

theorem dig_encP' (σ : Equiv.Perm (Fin 8)) (k : ℕ) (hk : k < 8) :
    dig (encP σ) k = (σ ⟨k, hk⟩).val := by
  obtain ⟨k0, k1, k2, k3, k4, k5, k6, k7⟩ :=
    dig_enc8 (σ 0).val (σ 1).val (σ 2).val (σ 3).val (σ 4).val (σ 5).val (σ 6).val (σ 7).val
      (σ 0).isLt (σ 1).isLt (σ 2).isLt (σ 3).isLt (σ 4).isLt (σ 5).isLt (σ 6).isLt (σ 7).isLt
  unfold encP
  interval_cases k
  · exact k0
  · exact k1
  · exact k2
  · exact k3
  · exact k4
  · exact k5
  · exact k6
  · exact k7

theorem dig_encP (σ : Equiv.Perm (Fin 8)) (i : Fin 8) : dig (encP σ) i.val = (σ i).val :=
  dig_encP' σ i.val i.isLt

theorem encP_injective : Function.Injective encP := by
  intro σ τ h
  ext i
  rw [← dig_encP σ i, ← dig_encP τ i, h]

theorem idC_eq : idC () = encP 1 := by
  unfold idC encP
  rfl

theorem mulC_encP (σ τ : Equiv.Perm (Fin 8)) : mulC (encP σ) (encP τ) = encP (σ * τ) := by
  have h : ∀ (k : ℕ) (hk : k < 8), dig (encP σ) (dig (encP τ) k) = ((σ * τ) ⟨k, hk⟩).val := by
    intro k hk
    simp only [dig_encP' τ k hk, dig_encP, Equiv.Perm.mul_apply]
  unfold mulC
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)] <;> rfl

theorem powC_encP (σ : Equiv.Perm (Fin 8)) (n : ℕ) : powC (encP σ) n = encP (σ ^ n) := by
  induction n with
  | zero =>
    rw [powC, pow_zero]
    exact idC_eq
  | succ n ih =>
    rw [powC, ih, mulC_encP, pow_succ]

end CFSG.Quasithin.H13.NPLSound

end
