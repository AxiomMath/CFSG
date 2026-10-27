module

public import CFSG.RankThree.PartOne.KE6.Phi6Arith

public section

namespace CFSG.RankThree.PartOne.KE6

theorem padicValNat_twistedE6_order_six {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hq : 2 ≤ q)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1) :
    padicValNat p (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) = 3 * padicValNat p (q ^ 2 - q + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpq, hord, hx, hq1, -, hQ2, hQ3, hQ4⟩ := e6Six_data hp hp3 h
  set Q : ZMod p := (q : ZMod p) with hQdef
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 2 p).not.mpr (fun h => absurd (Nat.le_of_dvd (by norm_num) h)
      (by omega))
    exact_mod_cast this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 3 p).not.mpr (fun h => absurd (Nat.le_of_dvd (by norm_num) h)
      (by omega))
    exact_mod_cast this
  have hQ0 : Q ≠ 0 := fun h0 => hpq ((ZMod.natCast_eq_zero_iff q p).1 h0)
  have hQ1 : Q ≠ 1 := fun h1 => hq1 (by
    have : (((q : ℤ) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [← hQdef, h1, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this)
  have hQ3'' : Q ^ 3 + 1 = 0 := by linear_combination (Q + 1) * hx
  have hQ6 : Q ^ 6 = 1 := by linear_combination (Q ^ 3 - 1) * hQ3''
  have hQ2' : Q ^ 2 = Q - 1 := by linear_combination hx
  have hQ2ne : Q ≠ 2 := fun h2' => h3 (by
    rw [h2'] at hx
    linear_combination hx)
  have hle2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hle3 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have nd : ∀ x : ℕ, (x : ZMod p) ≠ 0 → padicValNat p x = 0 := fun x hx =>
    padicValNat.eq_zero_of_not_dvd fun h => hx ((ZMod.natCast_eq_zero_iff x p).mpr h)
  have hcast : ∀ n : ℕ, 1 ≤ n → (((q ^ n - 1 : ℕ)) : ZMod p) = Q ^ n - 1 := fun n hn => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have e6 : q ^ 6 - 1 = (q - 1) * (q + 1) * (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
    zify [Nat.one_le_pow 6 q (by omega), (by omega : 1 ≤ q), hle2]
    ring
  have e12 : q ^ 12 - 1 = (q ^ 6 - 1) * (q ^ 6 + 1) := by
    zify [Nat.one_le_pow 12 q (by omega), Nat.one_le_pow 6 q (by omega)]
    ring
  have e9 : q ^ 9 + 1 = (q + 1) * (q ^ 2 - q + 1) * (q ^ 6 - q ^ 3 + 1) := by
    zify [hle2, hle3]
    ring
  have hA : 0 < q ^ 2 - q + 1 := Nat.succ_pos _
  have hq1' : 0 < q - 1 := by omega
  have hq2' : 0 < q ^ 2 + q + 1 := Nat.succ_pos _
  have hB : 0 < q ^ 6 - q ^ 3 + 1 := Nat.succ_pos _
  have hm : ∀ a b : ℕ, 0 < a → 0 < b → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
    fun a b ha hb => padicValNat.mul ha.ne' hb.ne'
  have v36 : padicValNat p (q ^ 36) = 0 := nd _ (by push_cast; exact pow_ne_zero _ hQ0)
  have vq1 : padicValNat p (q - 1) = 0 := nd _ (by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    exact sub_ne_zero.mpr hQ1)
  have vq1p : padicValNat p (q + 1) = 0 := nd _ (by push_cast; exact hQ2)
  have vq2 : padicValNat p (q ^ 2 + q + 1) = 0 := nd _ (by push_cast; exact hQ3)
  have vq6 : padicValNat p (q ^ 6 + 1) = 0 := nd _ (by push_cast; exact hQ4)
  have vB : padicValNat p (q ^ 6 - q ^ 3 + 1) = 0 := nd _ (by
    push_cast [Nat.cast_sub hle3]
    have e : Q ^ 6 - Q ^ 3 + 1 = 3 := by linear_combination hQ6 - hQ3''
    rw [e]
    exact h3)
  have v8 : padicValNat p (q ^ 8 - 1) = 0 := nd _ (by
    rw [hcast 8 (by norm_num)]
    intro h0
    exact hQ2ne (by linear_combination h0 - Q ^ 2 * hQ6 - hx))
  have v5 : padicValNat p (q ^ 5 + 1) = 0 := nd _ (by
    push_cast
    intro h0
    exact hQ2ne (by linear_combination Q ^ 2 * hQ3'' - hx - h0))
  have v2 : padicValNat p (q ^ 2 - 1) = 0 := nd _ (by
    rw [hcast 2 (by norm_num)]
    intro h0
    exact hQ2ne (by linear_combination h0 - hx))
  have pA6 : 0 < (q - 1) * (q + 1) * (q ^ 2 + q + 1) :=
    Nat.mul_pos (Nat.mul_pos hq1' (by omega)) hq2'
  have p6 : 0 < q ^ 6 - 1 := by
    have : 2 ≤ q ^ 6 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  have p36 : 0 < q ^ 36 := pow_pos (by omega) _
  have p12 : 0 < q ^ 12 - 1 := by
    have : 2 ≤ q ^ 12 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  have p9 : 0 < q ^ 9 + 1 := Nat.succ_pos _
  have p8 : 0 < q ^ 8 - 1 := by
    have : 2 ≤ q ^ 8 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  have p5 : 0 < q ^ 5 + 1 := Nat.succ_pos _
  have p2 : 0 < q ^ 2 - 1 := by
    have : 2 ≤ q ^ 2 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  have p66 : 0 < q ^ 6 + 1 := Nat.succ_pos _
  have vS : padicValNat p (q ^ 6 - 1) = padicValNat p (q ^ 2 - q + 1) := by
    rw [e6, hm _ _ pA6 hA, hm _ _ (Nat.mul_pos hq1' (by omega)) hq2', hm _ _ hq1' (by omega),
      vq1, vq1p, vq2]
    simp
  have vT : padicValNat p (q ^ 12 - 1) = padicValNat p (q ^ 2 - q + 1) := by
    rw [e12, hm _ _ p6 p66, vq6, add_zero, vS]
  have vU : padicValNat p (q ^ 9 + 1) = padicValNat p (q ^ 2 - q + 1) := by
    rw [e9, hm _ _ (Nat.mul_pos (by omega) hA) hB, hm _ _ (by omega) hA, vB, vq1p]
    simp
  have pX1 : 0 < q ^ 36 * (q ^ 12 - 1) := Nat.mul_pos p36 p12
  have pX2 := Nat.mul_pos pX1 p9
  have pX3 := Nat.mul_pos pX2 p8
  have pX4 := Nat.mul_pos pX3 p6
  have pX5 := Nat.mul_pos pX4 p5
  rw [hm _ _ pX5 p2, hm _ _ pX4 p5, hm _ _ pX3 p6, hm _ _ pX2 p8, hm _ _ pX1 p9, hm _ _ p36 p12,
    v36, vT, vU, v8, vS, v5, v2]
  ring

end CFSG.RankThree.PartOne.KE6
