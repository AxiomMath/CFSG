module

public import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Open (ordTwistedA)
open Matrix

theorem ordTwistedA_two_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  rw [ordTwistedA, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl, Finset.prod_pair (by norm_num),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq even_two,
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide)]

theorem padicValNat_ordTwistedA_two {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (ordTwistedA 2 (2 ^ m)) = 3 * m := by
  obtain ⟨s, hs, hseq⟩ :=
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := m) le_rfl hm).two
  rw [hseq, padicValNat.mul (by positivity) hs.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hs.not_two_dvd_nat, add_zero]
  show m * 3 = 3 * m
  exact Nat.mul_comm m 3

theorem ordTwistedA_two_lt {m : ℕ} (hm : 1 ≤ m) : ordTwistedA 2 (2 ^ m) < 2 ^ (8 * m) := by
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hlt : ∀ q : ℕ, 2 ≤ q → q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) < q ^ 8 := by
    intro q hq
    obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
    have h1 : 1 ≤ (t + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1]
    have : (0 : ℤ) < ((t : ℤ) + 2) ^ 8 -
        ((t : ℤ) + 2) ^ 3 * ((((t : ℤ) + 2) ^ 2 - 1) * (((t : ℤ) + 2) ^ 3 + 1)) := by
      ring_nf
      positivity
    linarith
  rw [ordTwistedA_two_eq (by omega)]
  calc _ ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := Nat.div_le_self _ _
    _ < (2 ^ m) ^ 8 := hlt _ hq
    _ = 2 ^ (8 * m) := by rw [← pow_mul, mul_comm]

open CFSG.Assembly.RankThreeEven (projSU) in
theorem card_projSU_three_two {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (projSU 3 2 m) = ordTwistedA 2 (2 ^ m) := by
  have h₀ : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
    ⟨Nat.prime_two, hm, GaloisField.card 2 _ (by omega)⟩
  exact (Nat.card_congr ((Census.statedSUEquivProjSU 3 2 m).symm.trans
    (unitaryPSUEquiv h₀ (by norm_num)).symm).toEquiv).trans (card_unitaryPSU_three_eq h₀)

open CFSG.Assembly.RankThreeEven (projSU) in
theorem padicValNat_card_and_card_cube_lt {X : Type*} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (e : X ≃* projSU 3 2 m) :
    padicValNat 2 (Nat.card X) = 3 * m ∧
      Nat.card X ^ 3 < 2 ^ (8 * padicValNat 2 (Nat.card X)) := by
  rw [(Nat.card_congr e.toEquiv).trans (card_projSU_three_two hm), padicValNat_ordTwistedA_two hm]
  refine ⟨rfl, ?_⟩
  calc ordTwistedA 2 (2 ^ m) ^ 3 < (2 ^ (8 * m)) ^ 3 :=
        Nat.pow_lt_pow_left (ordTwistedA_two_lt hm) (by norm_num)
    _ = 2 ^ (8 * (3 * m)) := by rw [← pow_mul]; ring_nf

theorem odd_card_and_three_le_of_ringChar_ne_two {K : Type*} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) : Odd (Nat.card K) ∧ 3 ≤ Nat.card K := by
  have := Fintype.ofFinite K
  have h1 := FiniteField.odd_card_of_char_ne_two hK
  have h2 : 1 < Nat.card K := Finite.one_lt_card
  rw [Nat.card_eq_fintype_card] at h2 ⊢
  exact ⟨Nat.odd_iff.mpr h1, by omega⟩

theorem card_psl_mul_gcd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin n) K) * Nat.gcd (Nat.card K - 1) n =
      Nat.card K ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1) := by
  rw [← LinearFlag.card_SL_eq hn,
    (Subgroup.center (SpecialLinearGroup (Fin n) K)).card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, hn⟩ : Fin n)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, Fintype.card_fin]

theorem card_psl_two_mul_two {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    Nat.card (CFSG.GorensteinWalter.PSL2 K) * 2 = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h := card_psl_mul_gcd (K := K) (n := 2) (by norm_num)
  obtain ⟨k, hk⟩ := (odd_card_and_three_le_of_ringChar_ne_two hK).1
  rw [Nat.gcd_eq_right (show 2 ∣ Nat.card K - 1 from ⟨k, by omega⟩),
    show Finset.Icc 2 2 = {2} by rfl, Finset.prod_singleton] at h
  simpa using h

theorem card_projectiveSL_mul_card_scalars {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) :
    Nat.card (LinearFlag.projectiveSL n K) * Nat.card (LinearFlag.scalars n K) =
      Nat.card K ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1) := by
  rw [← LinearFlag.card_SL_eq hn,
    (LinearFlag.scalars n K).card_eq_card_quotient_mul_card_subgroup]

theorem card_unitaryPSU_three_mul_gcd {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) :
    Nat.card (unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [← card_unitarySU_three h, ← card_unitaryScalars h (by norm_num),
    (unitaryScalars h 3).card_eq_card_quotient_mul_card_subgroup]

theorem odd_pow_and_one_lt_of_unitaryFieldData {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hK : ringChar K ≠ 2) : Odd (p ^ f) ∧ 1 < p ^ f := by
  have : CharP K p := h.charP
  have hp2 : p ≠ 2 := by rwa [ringChar.eq K p] at hK
  exact ⟨(h.prime.odd_of_ne_two hp2).pow,
    Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt⟩

open CFSG.Assembly.RankThreeEven (projSU) in
theorem not_oddCharStdModel_of_mulEquiv_projSU {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m)
    (e : X ≃* projSU 3 2 m) : ¬ OddCharStdModel X := by
  rintro ⟨K, _, _, hK2, hX⟩
  obtain ⟨hv, hlt⟩ := padicValNat_card_and_card_cube_lt (by omega) e
  have hcard : Nat.card X = ordTwistedA 2 (2 ^ m) :=
    (Nat.card_congr e.toEquiv).trans (card_projSU_three_two (by omega))
  have key : ∀ {Y : Type} [Group Y], Nonempty (X ≃* Y) →
      (6 ≤ padicValNat 2 (Nat.card Y) → 2 ^ (8 * padicValNat 2 (Nat.card Y)) ≤ Nat.card Y ^ 3) →
        False := by
    rintro Y _ ⟨e'⟩ hY
    rw [← Nat.card_congr e'.toEquiv] at hY
    have := hY (by omega)
    omega
  obtain ⟨hq, hq3⟩ := odd_card_and_three_le_of_ringChar_ne_two hK2
  rcases hX with hY | ⟨n, hn, hY⟩ | ⟨n, hn, hY⟩ | ⟨r, hr, hY⟩ | hY | ⟨p, f, h, hY | hY⟩
  · exact key hY (two_pow_le_of_mul_two_eq_psl_two hq (by omega) (card_psl_two_mul_two hK2))
  · exact key hY fun _ => two_pow_le_of_mul_eq_slOrd hq hq3 hn
      (card_projectiveSL_mul_card_scalars (by omega)) (LinearFlag.card_scalars_dvd (by omega))
  · exact key hY fun _ => two_pow_le_of_mul_eq_slOrd hq hq3 hn
      (by rw [mul_one]; exact LinearFlag.card_SL_eq (by omega)) (one_dvd _)
  · have hc := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero
      (Ring.two_ne_zero hK2) (by omega : 1 ≤ r)
    by_cases h23 : r = 2 ∧ Nat.card K = 3
    ·
      obtain ⟨rfl, hK3⟩ := h23
      obtain ⟨e'⟩ := hY
      have hN : Nat.card (StatedProj (StatedSp 2 K)) = 25920 := by
        rw [hK3, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)] at hc
        norm_num at hc
        omega
      have hX : Nat.card X = 25920 := (Nat.card_congr e'.toEquiv).trans hN
      have h6 : padicValNat 2 25920 = 6 := by
        rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
          padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd (by norm_num)]
      rw [hX, h6] at hv
      obtain rfl : m = 2 := by omega
      have h62400 := hcard.symm.trans hX
      rw [ordTwistedA_two_eq (by norm_num)] at h62400
      exact absurd h62400 (by decide)
    · have := Nat.odd_iff.mp hq
      exact key hY fun _ => two_pow_le_of_mul_two_eq_spOrd hq hq3 (by omega) hc
  · have hG2 := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)
    exact key hY fun _ => by
      rw [hG2]
      exact two_pow_le_g2 hq hq3
  · obtain ⟨hpq, hp1⟩ := odd_pow_and_one_lt_of_unitaryFieldData h hK2
    exact key hY (two_pow_le_of_mul_eq_su3 hpq hp1 (card_unitaryPSU_three_mul_gcd h)
      (Nat.gcd_dvd_left _ _))
  · obtain ⟨hpq, hp1⟩ := odd_pow_and_one_lt_of_unitaryFieldData h hK2
    exact key hY (two_pow_le_of_mul_eq_su3 hpq hp1
      (by rw [mul_one]; exact card_unitarySU_three h) (one_dvd _))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

open CFSG.Assembly.RankThreeEven (projSU) in
theorem exists_data83_of_projSU' {A : Subgroup G} {c : G} {a : G}
    (h : Sec8.Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * n))) :
    ∃ (A₀ : Subgroup G) (d : G), Sec8.Data83 G c L a A₀ d n :=
  exists_data83_of_projSU h hn hL (hL.elim fun e =>
    not_oddCharStdModel_of_mulEquiv_projSU (by have := hn.pos; omega) e)

end CFSG.RankThree.PartTwo.KFacts
