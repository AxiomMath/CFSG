module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.Open.Defs
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem toNat_factor_le_twAOrder {q q' : ℕ} (h : q ≤ q') (i : ℕ) :
    ((q : ℤ) ^ i - (-1) ^ i).toNat ≤ ((q' : ℤ) ^ i - (-1) ^ i).toNat := by
  have : (q : ℤ) ^ i ≤ (q' : ℤ) ^ i := pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) i
  exact Int.toNat_le_toNat (by linarith)

private theorem ordTwistedA_le_of_le_twAOrder {m q q' : ℕ} (h : q ≤ q')
    (hg : Nat.gcd (m + 1) (q' + 1) ≤ Nat.gcd (m + 1) (q + 1)) :
    CFSG.Open.ordTwistedA m q ≤ CFSG.Open.ordTwistedA m q' := by
  unfold CFSG.Open.ordTwistedA
  exact Nat.div_le_div (Nat.mul_le_mul (Nat.pow_le_pow_left h _)
    (Finset.prod_le_prod' fun i _ => toNat_factor_le_twAOrder h i)) hg
    (Nat.gcd_pos_of_pos_left _ m.succ_pos).ne'

private theorem two_pow_mod_six_twAOrder (k : ℕ) :
    2 ^ (2 * k + 1) % 6 = 2 ∧ 2 ^ (2 * k + 2) % 6 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : 2 ^ (2 * (k + 1) + 1) = 2 ^ (2 * k + 1) * 4 := by ring
    have e2 : 2 ^ (2 * (k + 1) + 2) = 2 ^ (2 * k + 2) * 4 := by ring
    rw [e1, e2]
    omega

private theorem gcd_six_of_odd_twAOrder {m : ℕ} (hm : Odd m) : Nat.gcd 6 (2 ^ m + 1) = 3 := by
  obtain ⟨k, rfl⟩ := hm
  have h := (two_pow_mod_six_twAOrder k).1
  rw [Nat.gcd_rec 6 (2 ^ (2 * k + 1) + 1), show (2 ^ (2 * k + 1) + 1) % 6 = 3 by omega]
  norm_num

private theorem gcd_six_le_twAOrder {g n : ℕ} (hn : 1 ≤ n) (hgn : g ∣ n) :
    Nat.gcd 6 (2 ^ n + 1) ≤ Nat.gcd 6 (2 ^ g + 1) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := (two_pow_mod_six_twAOrder j).2
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, Nat.gcd_rec 6 (2 ^ (2 * j + 2) + 1),
      show (2 ^ (2 * j + 2) + 1) % 6 = 5 by omega]
    calc Nat.gcd 5 6 = 1 := by norm_num
      _ ≤ Nat.gcd 6 (2 ^ g + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  · rw [gcd_six_of_odd_twAOrder (odd_two_mul_add_one k),
      gcd_six_of_odd_twAOrder (Odd.of_dvd_nat (odd_two_mul_add_one k) hgn)]

private theorem ordTwistedA_five_le_twAOrder {g n : ℕ} (hn : 1 ≤ n) (hgn : g ∣ n) :
    CFSG.Open.ordTwistedA 5 (2 ^ g) ≤ CFSG.Open.ordTwistedA 5 (2 ^ n) :=
  ordTwistedA_le_of_le_twAOrder (Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hn hgn))
    (gcd_six_le_twAOrder hn hgn)

private theorem pow_fifteen_le_ordTwistedA_five_twAOrder {q : ℕ} (hq : 2 ≤ q) :
    q ^ 15 ≤ CFSG.Open.ordTwistedA 5 q := by
  unfold CFSG.Open.ordTwistedA
  have hpos : 0 < Nat.gcd (5 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [Nat.le_div_iff_mul_le hpos, show 5 * (5 + 1) / 2 = 15 from rfl]
  refine Nat.mul_le_mul_left _ ((Nat.gcd_le_left _ (by norm_num)).trans ?_)
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have h1 : ∀ i ∈ Finset.Icc 2 (5 + 1), 1 ≤ ((q : ℤ) ^ i - (-1) ^ i).toNat := by
    intro i hi
    have hi1 : i ≠ 0 := by simp only [Finset.mem_Icc] at hi; omega
    have h2 : (2 : ℤ) ≤ (q : ℤ) ^ i := hq'.trans (le_self_pow₀ (by linarith) hi1)
    refine Nat.succ_le_of_lt (Int.lt_toNat.2 ?_)
    rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> push_cast <;> linarith
  have h3 : 5 + 1 ≤ ((q : ℤ) ^ 3 - (-1) ^ 3).toNat := by
    have h8 : (8 : ℤ) ≤ (q : ℤ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hq' 3
      norm_num at this
      exact this
    exact (Int.le_toNat (by norm_num; linarith)).2 (by push_cast; norm_num; linarith)
  exact h3.trans (Finset.single_le_prod' h1 (by decide))

private theorem ordTwistedA_two_le_twAOrder {q : ℕ} (hq : 2 ≤ q) :
    CFSG.Open.ordTwistedA 2 q ≤ q ^ 11 := by
  unfold CFSG.Open.ordTwistedA
  refine (Nat.div_le_self _ _).trans ?_
  rw [show 2 * (2 + 1) / 2 = 3 from rfl, show q ^ 11 = q ^ 3 * (q ^ 4) ^ 2 by ring]
  refine Nat.mul_le_mul_left _ ((Finset.prod_le_pow_card _ _ (q ^ 4) fun i hi => ?_).trans ?_)
  · have hi3 : i ≤ 3 := by simp only [Finset.mem_Icc] at hi; omega
    have hq' : (1 : ℤ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have h1 : (q : ℤ) ^ i ≤ (q : ℤ) ^ 3 := pow_le_pow_right₀ hq' hi3
    have h2 : (q : ℤ) ^ 3 + 1 ≤ (q : ℤ) ^ 4 := by nlinarith [pow_pos (by linarith : (0 : ℤ) < q) 3]
    refine Int.toNat_le.2 ?_
    push_cast
    rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> linarith
  · rw [Nat.card_Icc]

private theorem ordTwistedA_two_lt_five_twAOrder {q q' : ℕ} (hq : 2 ≤ q) (h : q ≤ q') :
    CFSG.Open.ordTwistedA 2 q < CFSG.Open.ordTwistedA 5 q' :=
  calc CFSG.Open.ordTwistedA 2 q ≤ q ^ 11 := ordTwistedA_two_le_twAOrder hq
    _ < q ^ 15 := Nat.pow_lt_pow_right hq (by norm_num)
    _ ≤ q' ^ 15 := Nat.pow_le_pow_left h 15
    _ ≤ CFSG.Open.ordTwistedA 5 q' := pow_fifteen_le_ordTwistedA_five_twAOrder (hq.trans h)

private theorem card_largeEvenProj_SU_twAOrder {N g : ℕ} (hN : 1 ≤ N) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) :
    1 ≤ g ∧ Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) =
      CFSG.Open.ordTwistedA N (2 ^ g) := by
  have hg : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  refine ⟨hg, ?_⟩
  change Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU (N + 1) (2 ^ g) K)) = _
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hg hK (by omega),
    CFSG.Open.ordTwistedA, Nat.add_sub_cancel, Nat.mul_comm (N + 1) N]

theorem largeEvenLabelAll_twA_not_marking_twA_five {lab : LargeEvenLabel}
    (htag : lab.tag = .twA) (hrank : lab.rank = 2 ∨ lab.rank = 5) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) := by
  obtain ⟨t, N, g⟩ := lab
  dsimp only at htag hrank ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun J₁ n hJ hgn hmark => ?_⟩
  obtain ⟨hg, hR⟩ := card_largeEvenProj_SU_twAOrder (N := N)
    (by rcases hrank with rfl | rfl <;> norm_num) hK
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨_, _, _, _, -, -, -, rfl⟩ := largeEvenRawDatum_exists hraw
  have hn : 1 ≤ n := hlab'.1
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K', i1', i2', hK', -, -, θ, -⟩ := hraw
  obtain ⟨-, hJR⟩ := card_largeEvenProj_SU_twAOrder (N := 5) (by norm_num) hK'
  have : Finite (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g)) := Subtype.finite
  have : Finite (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have h1 : Nat.card (↥J₁ ⧸ Subgroup.center ↥J₁) ≤ Nat.card J₁ :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card J₁ < Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin (N + 1)) K (2 ^ g))) :=
    lt_of_le_of_ne (Subgroup.card_le_card_group J₁) fun h => hJ (Subgroup.eq_top_of_card_eq J₁ h)
  rw [Nat.card_congr θ.toEquiv, hJR] at h1
  rw [hR] at h2
  have h3 : CFSG.Open.ordTwistedA N (2 ^ g) ≤ CFSG.Open.ordTwistedA 5 (2 ^ n) := by
    rcases hrank with rfl | rfl
    · exact (ordTwistedA_two_lt_five_twAOrder (Nat.one_lt_two_pow (by omega))
        (Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hn hgn))).le
    · exact ordTwistedA_five_le_twAOrder hn hgn
  omega

end CFSG.StandardType.SCFourCover

end
