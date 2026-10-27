module

public import CFSG.Quasithin.Vol2.F134LieF4Borel

public section

namespace CFSG.Quasithin.S146zY.TwoF4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.ABGLocalTools CFSG.Quasithin.F134.LieF4

theorem not_five_dvd_two_pow_sub_one (a : ℕ) : ¬ 5 ∣ 2 ^ (2 * a + 1) - 1 := by
  have h : 2 ^ (2 * a + 1) % 5 = 2 ∨ 2 ^ (2 * a + 1) % 5 = 3 := by
    induction a with
    | zero => simp
    | succ k ih =>
      have : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pow_add]
        ring
      omega
  have hpos : 0 < 2 ^ (2 * a + 1) := by positivity
  omega


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem eq_one_of_mem_reeFixedBorel_five (hK : ¬ 5 ∣ Nat.card K - 1) {x : ModGL F4.tag K}
    (hx : x ∈ F4.reeFixedBorel K a) (h5 : x ^ 5 = 1) : x = 1 := by
  have h1 := pow_card_sub_one_mem_reeFixedPosUnipotent hx
  have hp : IsPGroup 2 (F4.reeFixedPosUnipotent K a) :=
    (isPGroup_posUnipotent 2 F4.tag).to_le inf_le_left
  obtain ⟨k, hk⟩ := hp ⟨_, h1⟩
  have h2 : (x ^ (Nat.card K - 1)) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : x ^ ((Nat.card K - 1) * 2 ^ k) = 1 := by
    rw [pow_mul]
    exact h2
  have hg : x ^ Nat.gcd ((Nat.card K - 1) * 2 ^ k) 5 = 1 := pow_gcd_eq_one.2 ⟨h3, h5⟩
  have hcop : Nat.gcd ((Nat.card K - 1) * 2 ^ k) 5 = 1 := by
    refine Nat.Coprime.symm (Nat.Coprime.mul_right ?_ (Nat.Coprime.pow_right _ (by norm_num)))
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hK
  rwa [hcop, pow_one] at hg

theorem false_of_le_reeGamma_five (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Q H P : Subgroup (ModGL F4.tag K)}
    (hBQ : F4.reeFixedBorel K a ≤ Q) (hQΓ : Q ≤ F4.reeGamma K a) (hQ : Q ≠ F4.reeGamma K a)
    (hHQ : H ≤ Q) (hUH : F4.reeFixedPosUnipotent K a ≤ H)
    (hH : Nat.card H = 25 * Nat.card (F4.reeFixedPosUnipotent K a)) (hPH : P ≤ H)
    (hP : Nat.card P = 25) (hexp : ∀ x ∈ P, x ^ 5 = 1) : False := by
  have : Finite (ModGL F4.tag K) := finite_modGL
  have hK5 : ¬ 5 ∣ Nat.card K - 1 := by
    rw [hK]
    exact not_five_dvd_two_pow_sub_one a
  obtain ⟨i, hi⟩ := exists_le_reeLocalParabolic hBQ hQΓ hQ
  have hrel : (F4.reeFixedPosUnipotent K a).relIndex H = 25 := by
    have h := Subgroup.relIndex_mul_card (F4.reeFixedPosUnipotent K a) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rcases le_reeFixedBorel_or_dvd (hHQ.trans hi) hUH with hB | hdvd
  · have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun x hx =>
      eq_one_of_mem_reeFixedBorel_five hK5 (hB (hPH hx)) (hexp x hx)
    rw [hbot, Subgroup.card_bot] at hP
    omega
  rw [hrel] at hdvd
  have hq8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨i, hi2⟩ := i
  have hi2' : i < 2 := hi2
  interval_cases i
  · rw [card_reeFixedOrbitUnipotent_zero hK] at hle hdvd
    obtain rfl : a = 1 := by
      by_contra ha1
      have : 2 ^ 5 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hK8 : Nat.card K = 8 := hK.trans (by norm_num)
    rw [hK8] at hdvd
    exact absurd hdvd (by norm_num)
  · rw [card_reeFixedOrbitUnipotent_one hK] at hle
    nlinarith

end CFSG.Quasithin.S146zY.TwoF4
