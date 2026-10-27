module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1MarkTriality
import CFSG.Assembly.GL83StatedBridge
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open TableB

private theorem ordA_one_le_twDTwo (x : ℕ) : ordA 1 x ≤ x ^ 3 := by
  show x ^ 1 * (∏ i ∈ Finset.Icc 2 2, (x ^ i - 1)) / Nat.gcd 2 (x - 1) ≤ x ^ 3
  rw [Finset.Icc_self, Finset.prod_singleton, pow_one]
  calc x * (x ^ 2 - 1) / Nat.gcd 2 (x - 1) ≤ x * (x ^ 2 - 1) := Nat.div_le_self _ _
    _ ≤ x * x ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = x ^ 3 := by ring

private theorem ordA_one_pos_twDTwo {g : ℕ} (hg : 1 ≤ g) : 0 < ordA 1 ((2 ^ g) ^ 2) := by
  show 0 < ((2 ^ g) ^ 2) ^ 1 * (∏ i ∈ Finset.Icc 2 2, (((2 ^ g) ^ 2) ^ i - 1)) /
    Nat.gcd 2 ((2 ^ g) ^ 2 - 1)
  rw [Finset.Icc_self, Finset.prod_singleton, pow_one]
  have h2 : 2 ≤ (2 ^ g) ^ 2 :=
    (Nat.le_self_pow (by omega) 2).trans (Nat.le_self_pow (by norm_num) _)
  have h4 : 4 ≤ ((2 ^ g) ^ 2) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left h2 2)
  refine Nat.div_pos ?_ (Nat.gcd_pos_of_pos_left _ (by norm_num))
  calc Nat.gcd 2 ((2 ^ g) ^ 2 - 1) ≤ 2 * 3 := (Nat.gcd_le_left _ (by norm_num)).trans (by norm_num)
    _ ≤ (2 ^ g) ^ 2 * (((2 ^ g) ^ 2) ^ 2 - 1) := Nat.mul_le_mul h2 (by omega)

private theorem ordA_one_le_pow_six_twDTwo {g m : ℕ} (h : g ≤ m) :
    ordA 1 ((2 ^ g) ^ 2) ≤ (2 ^ m) ^ 6 :=
  calc ordA 1 ((2 ^ g) ^ 2) ≤ ((2 ^ g) ^ 2) ^ 3 := ordA_one_le_twDTwo _
    _ = (2 ^ g) ^ 6 := by ring
    _ ≤ (2 ^ m) ^ 6 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) h) 6

private theorem pow_six_le_ordD_four_twDTwo {q : ℕ} (hq : 2 ≤ q) : q ^ 6 ≤ ordD 4 q := by
  show q ^ 6 ≤ q ^ 12 * (q ^ 4 - 1) * (∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ 4 - 1)
  have hP : 0 < ∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1) := Finset.prod_pos fun i hi => by
    have h1 : q ≤ q ^ (2 * i) := Nat.le_self_pow (by have := (Finset.mem_Icc.1 hi).1; omega) q
    omega
  have h4 : 0 < q ^ 4 - 1 := by
    have h1 : q ≤ q ^ 4 := Nat.le_self_pow (by norm_num) q
    omega
  have h6 : 4 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by norm_num))]
  calc q ^ 6 * Nat.gcd 4 (q ^ 4 - 1) ≤ q ^ 6 * q ^ 6 :=
        Nat.mul_le_mul_left _ ((Nat.gcd_le_left _ (by norm_num)).trans h6)
    _ = q ^ 12 := by ring
    _ ≤ q ^ 12 * (q ^ 4 - 1) := Nat.le_mul_of_pos_right _ h4
    _ ≤ q ^ 12 * (q ^ 4 - 1) * ∏ i ∈ Finset.Icc 1 3, (q ^ (2 * i) - 1) :=
        Nat.le_mul_of_pos_right _ hP

private theorem pow_six_le_ordTrialityD4_twDTwo {q : ℕ} (hq : 2 ≤ q) :
    q ^ 6 ≤ ordTrialityD4 q := by
  show q ^ 6 ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  have h6 : 0 < q ^ 6 - 1 := by
    have h1 : q ≤ q ^ 6 := Nat.le_self_pow (by norm_num) q
    omega
  have h2 : 0 < q ^ 2 - 1 := by
    have h1 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    omega
  calc q ^ 6 ≤ q ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) := Nat.le_mul_of_pos_right _ h6
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
        Nat.le_mul_of_pos_right _ h2

private theorem pow_six_le_ordA_two_twDTwo {q : ℕ} (hq : 3 ≤ q) : q ^ 6 ≤ ordA 2 q := by
  show q ^ 6 ≤ q ^ 3 * (∏ i ∈ Finset.Icc 2 3, (q ^ i - 1)) / Nat.gcd 3 (q - 1)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have h2 : 9 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have h3 : 27 ≤ q ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by norm_num))]
  calc q ^ 6 * Nat.gcd 3 (q - 1) ≤ q ^ 6 * 3 :=
        Nat.mul_le_mul_left _ (Nat.gcd_le_left _ (by norm_num))
    _ = q ^ 3 * (q ^ 3 * 3) := by ring
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
        refine Nat.mul_le_mul_left _ ?_
        calc q ^ 3 * 3 ≤ 8 * (q ^ 3 - 1) := by omega
          _ ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul_right _ (by omega)

private theorem pow_six_le_ordTwistedA_two_twDTwo {q : ℕ} (hq : 3 ≤ q) :
    q ^ 6 ≤ ordTwistedA 2 q := by
  show q ^ 6 ≤ q ^ 3 * (∏ i ∈ Finset.Icc 2 3, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) /
    Nat.gcd 3 (q + 1)
  have e2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [this, Int.toNat_natCast]
  have e3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num), e2, e3]
  have h2 : 9 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  rw [Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_left _ (by norm_num))]
  calc q ^ 6 * Nat.gcd 3 (q + 1) ≤ q ^ 6 * 3 :=
        Nat.mul_le_mul_left _ (Nat.gcd_le_left _ (by norm_num))
    _ = q ^ 3 * (q ^ 3 * 3) := by ring
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
        refine Nat.mul_le_mul_left _ ?_
        calc q ^ 3 * 3 ≤ 8 * (q ^ 3 + 1) := by omega
          _ ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := Nat.mul_le_mul_right _ (by omega)

private theorem three_le_two_pow_three_mul_twDTwo {n : ℕ} (hn : 1 ≤ n) : 3 ≤ 2 ^ (3 * n) :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 3 * n))

private theorem largeEvenLabelAll_card_twDTwo {lab : LargeEvenLabel} (htag : lab.tag = .twD)
    (hr : lab.rank = 2) :
    LargeEvenLabelAll lab fun R _ _ _ => Nat.card R = ordA 1 ((2 ^ lab.n) ^ 2) := by
  obtain ⟨t, N, g⟩ := lab
  dsimp only at htag hr ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_pos hr] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  show Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) = ordA 1 ((2 ^ g) ^ 2)
  rw [largeEvenSLGroup_eq_statedSL, ← hK]
  exact CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num)

theorem ggInndiagOnCompAt_twD_two_dPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twD) (hr : lab.rank = 2) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ :=
  ggInndiagOnCompAt_of_noJ1 hlab (fun n => n)
    (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
    (largeEvenLabelAll_noJ1_dPair_of_card (largeEvenLabelAll_card_twDTwo htag hr)
      (ordA_one_pos_twDTwo hlab.1)
      (fun n hn _ hd => Or.inr ((ordA_one_le_pow_six_twDTwo (Nat.le_of_dvd hn hd)).trans
        (pow_six_le_ordD_four_twDTwo (Nat.le_self_pow (by omega) 2))))
      (fun n hn _ hd => Or.inr ((ordA_one_le_pow_six_twDTwo (Nat.le_of_dvd hn hd)).trans
        (pow_six_le_ordTrialityD4_twDTwo (Nat.le_self_pow (by omega) 2)))))

theorem ggInndiagOnCompAt_twD_two_aPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twD) (hr : lab.rank = 2) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ :=
  ggInndiagOnCompAt_of_noJ1 hlab (fun n => 3 * n)
    (fun _ _ h => by rcases h with rfl | rfl <;> exact ⟨by simp, rfl⟩)
    (largeEvenLabelAll_noJ1_aPair_of_card (largeEvenLabelAll_card_twDTwo htag hr)
      (ordA_one_pos_twDTwo hlab.1)
      (fun n hn _ hd => Or.inr ((ordA_one_le_pow_six_twDTwo (Nat.le_of_dvd (by omega) hd)).trans
        (pow_six_le_ordA_two_twDTwo (three_le_two_pow_three_mul_twDTwo hn))))
      (fun n hn _ hd => Or.inr ((ordA_one_le_pow_six_twDTwo (Nat.le_of_dvd (by omega) hd)).trans
        (pow_six_le_ordTwistedA_two_twDTwo (three_le_two_pow_three_mul_twDTwo hn)))))

end CFSG.StandardType.SCFourCover

end
