module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofAfter
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Open (ordTrialityD4)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (projSU projSp)

theorem padicValNat_two_pow_mul_odd {a r : ℕ} (hr : Odd r) : padicValNat 2 (2 ^ a * r) = a := by
  have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
  rw [padicValNat.mul (by positivity) hr.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hr2, add_zero]

theorem ordTrialityD4_lt_sp4 {x : ℤ} (hx : 2 ≤ x) :
    x ^ 12 * ((x ^ 8 + x ^ 4 + 1) * (x ^ 6 - 1) * (x ^ 2 - 1)) <
      x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1)) := by
  have h : x ^ 12 * ((x ^ 6 - 1) * (x ^ 12 - 1)) -
      x ^ 12 * ((x ^ 8 + x ^ 4 + 1) * (x ^ 6 - 1) * (x ^ 2 - 1)) =
      x ^ 14 * (x ^ 6 - 1) * (x ^ 8 + x ^ 4 + 1) * (x ^ 2 - 1) := by ring
  have h14 : 0 < x ^ 14 := by positivity
  have h6 : 0 < x ^ 6 - 1 := by
    have : (2 : ℤ) ^ 6 ≤ x ^ 6 := pow_le_pow_left₀ (by norm_num) hx 6
    linarith
  have h8 : 0 < x ^ 8 + x ^ 4 + 1 := by positivity
  have h2 : 0 < x ^ 2 - 1 := by
    have : (2 : ℤ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
    linarith
  have hpos := mul_pos (mul_pos (mul_pos h14 h6) h8) h2
  linarith

theorem card_of_isoTrialityD4
    {X : Type} [Group X] {n : ℕ}
    (hn : 1 ≤ n)
    (h : IsoTrialityD4 X n) :
    Nat.card X = ordTrialityD4 (2 ^ n) ∧ padicValNat 2 (Nat.card X) = n * 12 := by
  obtain ⟨q, hv, hq2, hqe, ⟨e⟩⟩ := h
  have hcard : Nat.card X = ordTrialityD4 (2 ^ n) := by
    rw [Nat.card_congr e.toEquiv, Sec11.KSListsProof.card_trialityD4_carrier,
      TauCeti.PrimePower.card_def, hq2, hqe]
  refine ⟨hcard, ?_⟩
  rw [hcard, Sec19.Step1911Proof.ordTrialityD4_two_pow]
  exact padicValNat_two_pow_mul_odd (Sec19.Step1911Proof.odd_trialityOddPart hn)

theorem kF83D4Distinct :
    KF83D4Distinct := by
  intro X _ n hn hX
  have hn1 : 1 ≤ n := hn.pos
  obtain ⟨hcard, hv2⟩ := card_of_isoTrialityD4 hn1 hX
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rintro ⟨k, K, _, _, _, hk, hK, ⟨e⟩⟩
    have h1 := (LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion k K
      (by rw [hK, hk])).1
    obtain ⟨r, hr, hr'⟩ := exists_two_part_ree (q := 2 ^ (2 * k + 1)) (f := 2 * k + 1) rfl
      (by omega)
    have h2 : padicValNat 2 (Nat.card X) = (2 * k + 1) * 12 := by
      rw [Nat.card_congr e.toEquiv, h1, hr']
      exact padicValNat_two_pow_mul_odd hr
    omega
  ·
    rintro ⟨K, _, _, hK, ⟨e⟩⟩
    have hU : UnitaryFieldData 2 (3 * n) K :=
      ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
    have h1 : Nat.card X =
        (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1)) := by
      rw [Nat.card_congr e.toEquiv]
      rw [show (2 ^ (3 * n)) ^ 3 * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1)) =
        (2 ^ (3 * n)) ^ 3 * ((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1) by ring]
      exact card_unitarySU_three hU
    have hodd : Odd (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1)) :=
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
        (Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num))
    obtain ⟨r, hr⟩ : ∃ r, r = ((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1) := ⟨_, rfl⟩
    rw [← hr] at h1 hodd
    have h2 : padicValNat 2 (Nat.card X) = 3 * n * 3 := by
      rw [h1, ← pow_mul]
      exact padicValNat_two_pow_mul_odd hodd
    omega
  ·
    refine ⟨fun e => ?_⟩
    have := (padicValNat_card_and_card_cube_lt (by omega) e).1
    omega
  ·
    refine ⟨fun e => ?_⟩
    have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
    rw [Sec19.Step1911Proof.card_projSp_two (n := 3 * n) (by omega)] at h1
    have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    obtain ⟨q, hqdef⟩ : ∃ q, q = 2 ^ n := ⟨_, rfl⟩
    rw [← hqdef] at hq
    have e1 : 2 ^ (3 * n * 4) = q ^ 12 := by rw [hqdef, ← pow_mul]; ring_nf
    have e2 : (2 ^ (3 * n)) ^ 2 = q ^ 6 := by rw [hqdef, ← pow_mul, ← pow_mul]; ring_nf
    have e3 : (2 ^ (3 * n)) ^ 4 = q ^ 12 := by rw [hqdef, ← pow_mul, ← pow_mul]; ring_nf
    rw [e1, e2, e3, ← hqdef, ordTrialityD4] at h1
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    have h12 : 1 ≤ q ^ 12 := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h6, h12, h2] at h1
    have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
    have hlt := ordTrialityD4_lt_sp4 hq'
    linarith

end CFSG.RankThree.PartTwo.Sec8.Item83Proof

