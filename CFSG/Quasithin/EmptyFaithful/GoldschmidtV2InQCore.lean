module

public import CFSG.Quasithin.EmptyFaithful.S151ZY

public section

namespace CFSG.Quasithin

namespace V2InQ

variable {V : Type*} [CommGroup V]

theorem conj_pow_eq {z y q : MulAut V} (hqz : q * z = z * q) (hqy : q * y * q⁻¹ = z * y) (j : ℕ) :
    q ^ j * y * (q ^ j)⁻¹ = z ^ j * y := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcomm : Commute q (z ^ j) := (Commute.pow_right (show Commute q z from hqz) j)
    calc q ^ (j + 1) * y * (q ^ (j + 1))⁻¹ = q * (q ^ j * y * (q ^ j)⁻¹) * q⁻¹ := by
          rw [pow_succ']; simp [mul_assoc, mul_inv_rev]
      _ = q * (z ^ j * y) * q⁻¹ := by rw [ih]
      _ = (q * z ^ j * q⁻¹) * (q * y * q⁻¹) := by group
      _ = z ^ j * (z * y) := by rw [hcomm.eq, mul_inv_cancel_right, hqy]
      _ = z ^ (j + 1) * y := by rw [pow_succ']; group

theorem card_fixOf_conj (q g : MulAut V) : Nat.card (fixOf (q * g * q⁻¹)) = Nat.card (fixOf g) := by
  have h : fixOf (q * g * q⁻¹) = (fixOf g).map (q : V ≃* V).toMonoidHom := by
    ext w
    rw [Subgroup.mem_map]
    constructor
    · intro hw
      refine ⟨(q⁻¹ : MulAut V) w, ?_, ?_⟩
      · show g ((q⁻¹ : MulAut V) w) = (q⁻¹ : MulAut V) w
        have h1 : (q * g * q⁻¹) w = w := hw
        have h2 : (q⁻¹ : MulAut V) ((q * g * q⁻¹) w) = (q⁻¹ : MulAut V) w := by rw [h1]
        simpa [MulAut.mul_apply] using h2
      · simp
    · rintro ⟨u, hu, rfl⟩
      show (q * g * q⁻¹) (q u) = q u
      have hu' : g u = u := hu
      simp [MulAut.mul_apply, hu']
  rw [h]
  exact Subgroup.card_map_of_injective (q : V ≃* V).injective

theorem pow_apply_of_fix {g : MulAut V} {w : V} (hw : g w = w) (n : ℕ) : (g ^ n) w = w := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hw, ih]

variable [Finite V]

theorem card_fixOf_le {z y q : MulAut V} (hz3 : z ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hzfpf : ∀ w : V, z w = w → w = 1) (hzy : z * y = y * z) (hqz : q * z = z * q)
    (hqy : q * y * q⁻¹ = z * y) (hy4 : Nat.card (fixOf y) ≤ 4) {a b : ℕ}
    (hab : ¬ (3 ∣ a ∧ 3 ∣ b)) : Nat.card (fixOf (z ^ a * y ^ b)) ≤ 4 := by
  by_cases hb : 3 ∣ b
  · have ha : ¬ 3 ∣ a := fun ha => hab ⟨ha, hb⟩
    obtain ⟨b', rfl⟩ := hb
    have hyb : y ^ (3 * b') = 1 := by rw [pow_mul, hy3, one_pow]
    have hfix : fixOf (z ^ a * y ^ (3 * b')) = ⊥ := by
      rw [hyb, mul_one, eq_bot_iff]
      intro w hw
      exact (Subgroup.mem_bot).2 (fpf_pow_of_fpf hz3 hzfpf ha w hw)
    rw [hfix, Subgroup.card_bot]
    norm_num
  · have hb2 : b * b % 3 = 1 := by
      have : b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    have hzpow : ∀ m n : ℕ, m % 3 = n % 3 → z ^ m = z ^ n := fun m n h => by
      calc z ^ m = z ^ (3 * (m / 3) + m % 3) := by rw [Nat.div_add_mod]
        _ = z ^ (3 * (n / 3) + n % 3) := by
          rw [pow_add, pow_add, pow_mul, pow_mul, hz3]
          simp only [one_pow, one_mul, h]
        _ = z ^ n := by rw [Nat.div_add_mod]
    have hypow : ∀ m n : ℕ, m % 3 = n % 3 → y ^ m = y ^ n := fun m n h => by
      calc y ^ m = y ^ (3 * (m / 3) + m % 3) := by rw [Nat.div_add_mod]
        _ = y ^ (3 * (n / 3) + n % 3) := by
          rw [pow_add, pow_add, pow_mul, pow_mul, hy3]
          simp only [one_pow, one_mul, h]
        _ = y ^ n := by rw [Nat.div_add_mod]
    set k := a * b with hk
    have hconj : q ^ k * y ^ b * (q ^ k)⁻¹ = z ^ (k * b) * y ^ b := by
      have h1 : q ^ k * y ^ b * (q ^ k)⁻¹ = (q ^ k * y * (q ^ k)⁻¹) ^ b := by
        simp only [← MulAut.conj_apply, map_pow]
      rw [h1, conj_pow_eq hqz hqy k]
      have hc : Commute (z ^ k) y := Commute.pow_left (show Commute z y from hzy) k
      rw [hc.mul_pow, ← pow_mul]
    have hzk : z ^ (k * b) = z ^ a := by
      apply hzpow
      rw [hk, mul_assoc, Nat.mul_mod, hb2, mul_one, Nat.mod_mod]
    have hg : z ^ a * y ^ b = q ^ k * y ^ b * (q ^ k)⁻¹ := by rw [hconj, hzk]
    rw [hg, card_fixOf_conj]
    have hyy : y = (y ^ b) ^ b := by
      rw [← pow_mul]
      calc y = y ^ 1 := (pow_one y).symm
        _ = y ^ (b * b) := hypow 1 (b * b) (by rw [hb2])
    refine le_trans (Subgroup.card_le_of_le ?_) hy4
    intro w hw
    have hw' : (y ^ b) w = w := hw
    show y w = w
    rw [hyy]
    exact pow_apply_of_fix hw' b

end V2InQ

end CFSG.Quasithin
