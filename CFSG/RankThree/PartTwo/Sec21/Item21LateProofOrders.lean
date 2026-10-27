module

import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.HS
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.Ru
import CFSG.Sporadic.J4
import CFSG.Sporadic.J3
import CFSG.Timmesfeld.Orders.Classical
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.Models.PGLOrders
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21LateProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

theorem card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 :=
  CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_galoisField_two_zero

theorem card_SL3_zero : Nat.card (SL3 0) = 2 ^ 3 * 21 := by
  rw [SL3, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
    card_galoisField_two_zero]
  decide

theorem card_SL3_eq (n : ℕ) : ∃ r, Odd r ∧ Nat.card (SL3 n) = 2 ^ (3 * max n 1) * r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨21, by decide, by rw [card_SL3_zero]; norm_num⟩
  · refine ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1),
      (Timmesfeld.Orders.odd_pow_sub_one hn two_pos).mul
        (Timmesfeld.Orders.odd_pow_sub_one hn three_pos), ?_⟩
    rw [SL3, Sec19.Step1911Proof.card_SL3 hn, max_eq_left hn, mul_comm 3 n]

theorem card_projSL3_eq_of_pos {n : ℕ} (hn : 1 ≤ n) :
    ∃ r, Odd r ∧ Nat.card (projSL 3 (GaloisField 2 n)) = 2 ^ (3 * n) * r := by
  obtain ⟨r, hr, hm⟩ := (Timmesfeld.Orders.profile_ordA (n := 2) (f := n) (by norm_num) hn).two
  refine ⟨r, hr, ?_⟩
  rw [Sec19.Step1911Proof.card_projSL (by norm_num) hn, show 3 - 1 = 2 by rfl, hm]
  congr 2
  omega

theorem card_projSL3_zero : Nat.card (projSL 3 (GaloisField 2 0)) = 2 ^ 3 * 21 := by
  let φ : CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 3 (GaloisField 2 0)) ≃* projSL 3 (GaloisField 2 0) :=
    (Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSL_eq_projSL 3 _))
  rw [← Nat.card_congr φ.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (by norm_num), card_galoisField_two_zero]
  decide

theorem card_projSL3_eq (n : ℕ) :
    ∃ r, Odd r ∧ Nat.card (projSL 3 (GaloisField 2 n)) = 2 ^ (3 * max n 1) * r := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨21, by decide, by rw [card_projSL3_zero]; norm_num⟩
  · rw [max_eq_left hn]
    exact card_projSL3_eq_of_pos hn

theorem card_SL3_three : Nat.card (SL3 3) = 2 ^ 9 * 32193 := by
  rw [SL3, Sec19.Step1911Proof.card_SL3 (by norm_num)]
  norm_num

theorem card_SL3_seven : Nat.card (SL3 7) = 2 ^ 21 * 34357624833 := by
  rw [SL3, Sec19.Step1911Proof.card_SL3 (by norm_num)]
  norm_num

theorem card_projSL3_eq_card_SL3 {n : ℕ} (hn : 1 ≤ n) (ho : Odd n) :
    Nat.card (projSL 3 (GaloisField 2 n)) = Nat.card (SL3 n) := by
  have h := Sec19.Step1911Proof.ordA_two_mul_gcd n
  have hg : Nat.gcd 3 (2 ^ n - 1) = 1 := by
    have h4 : 2 ^ n % 3 = 2 := by
      obtain ⟨k, rfl⟩ := ho
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h5 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : ¬ 3 ∣ 2 ^ n - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  rw [hg, mul_one] at h
  rw [Sec19.Step1911Proof.card_projSL (by norm_num) hn, SL3, Sec19.Step1911Proof.card_SL3 hn,
    show 3 - 1 = 2 by rfl, h]

theorem card_projSU4_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ r, Odd r ∧ Nat.card (projSU 4 2 n) = 2 ^ (6 * n) * r := by
  refine ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1), odd_ordTwistedA_three_part hn,
    ?_⟩
  rw [card_projSU le_rfl hn, show 4 - 1 = 3 by rfl, ordTwistedA_three_eq hn, ← pow_mul,
    mul_comm n 6]

theorem card_of_isTripleCover {X Y : Type*} [Group X] [Group Y] (h : Sec4.IsTripleCover X Y) :
    Nat.card X = 3 * Nat.card Y := by
  obtain ⟨h3, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), h3,
    Nat.card_congr e.toEquiv, mul_comm]

theorem card_M22_eq : Nat.card NativeSporadic.M22 = 2 ^ 7 * 3465 := by
  rw [KFacts.KS14.card_nativeM22]
  norm_num

theorem card_M23_eq :
    Nat.card NativeSporadic.M23 = 2 ^ 7 * 79695 := by
  rw [CFSG.Sporadic.Schreier.m23_card]
  norm_num

theorem card_HS_eq : Nat.card NativeSporadic.HS = 2 ^ 9 * 86625 := by
  rw [CFSG.Sporadic.HS.card_HS]
  norm_num

theorem card_M24_eq :
    Nat.card NativeSporadic.M24 = 2 ^ 10 * 239085 := by
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

theorem card_He_eq :
    Nat.card NativeSporadic.He = 2 ^ 10 * 3935925 := by
  rw [CFSG.Sporadic.He.card_He]
  norm_num

theorem card_J2_eq : Nat.card NativeSporadic.J2 = 2 ^ 7 * 4725 := by
  rw [KFacts.KS14.card_nativeJ2]
  norm_num

theorem card_Ru_eq :
    Nat.card NativeSporadic.Ru = 2 ^ 14 * 8906625 := by
  rw [CFSG.Sporadic.Ru.card_Ru]
  norm_num

theorem card_J4_eq :
    Nat.card NativeSporadic.J4 = 2 ^ 21 * 41377816699065 := by
  rw [CFSG.Sporadic.J4.card_J4]
  norm_num

theorem card_J3_eq :
    Nat.card NativeSporadic.J3 = 2 ^ 7 * 392445 := by
  rw [CFSG.Sporadic.J3.card_J3]
  norm_num

theorem card_U54_eq : Nat.card (projSU 5 2 2) = 2 ^ 20 * 50968125 :=
  CFSG.PGLModel.card_projSU_five_four.trans (by norm_num)

theorem card_projSp2_eq {n : ℕ} (hn : 1 ≤ n) :
    ∃ r, Odd r ∧ Nat.card (projSp 2 (GaloisField 2 n)) = 2 ^ (4 * n) * r :=
  ⟨((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1),
    (Timmesfeld.Orders.odd_pow_sub_one hn two_pos).mul
      (Timmesfeld.Orders.odd_pow_sub_one hn four_pos),
    by rw [Sec19.Step1911Proof.card_projSp_two hn, mul_comm n 4]⟩

theorem card_PSL_two_eq {X : Type} [Group X] {m : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL m 2 1) :
    (m = 4 → Nat.card X = 2 ^ 6 * 315) ∧ (m = 5 → Nat.card X = 2 ^ 10 * 9765) := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  refine ⟨fun h4 => ?_, fun h5 => ?_⟩
  · subst h4
    rw [hc, show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide]
    norm_num
  · subst h5
    rw [hc, show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
    norm_num

theorem card_PSp_three_two_eq {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 3 2 1) :
    Nat.card X = 2 ^ 9 * 2835 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl,
    show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide]

theorem card_SL3_ne_ordG2 {m : ℕ} (hm : 1 ≤ m) :
    2 ^ (2 * m * 3) * (((2 ^ (2 * m)) ^ 2 - 1) * ((2 ^ (2 * m)) ^ 3 - 1)) ≠
      CFSG.Open.ordG2 (2 ^ m) := by
  unfold CFSG.Open.ordG2
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 2 ^ (2 * m * 3) = q ^ 6 := by rw [hq, ← pow_mul]; ring_nf
  have e2 : (2 ^ (2 * m)) ^ 2 = q ^ 4 := by rw [hq, ← pow_mul, ← pow_mul]; ring_nf
  have e3 : (2 ^ (2 * m)) ^ 3 = q ^ 6 := by rw [hq, ← pow_mul, ← pow_mul]; ring_nf
  rw [e1, e2, e3]
  intro h
  have h4 : q ^ 2 - 1 < q ^ 4 - 1 := by
    have : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right hq2 (by norm_num)
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h6 : 0 < q ^ 6 - 1 := by
    have : 2 ≤ q ^ 6 := le_trans hq2 (Nat.le_self_pow (by norm_num) q)
    omega
  have hq6 : 0 < q ^ 6 := by positivity
  have hlt : q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) < q ^ 6 * ((q ^ 4 - 1) * (q ^ 6 - 1)) := by
    rw [mul_assoc, mul_comm (q ^ 6 - 1) (q ^ 2 - 1)]
    exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right h4 h6) hq6
  omega

theorem three_mul_ordG2_lt {m : ℕ} (hm : 1 ≤ m) :
    3 * CFSG.Open.ordG2 (2 ^ m) <
      2 ^ (2 * m * 3) * (((2 ^ (2 * m)) ^ 2 - 1) * ((2 ^ (2 * m)) ^ 3 - 1)) := by
  unfold CFSG.Open.ordG2
  set q := 2 ^ m with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 2 ^ (2 * m * 3) = q ^ 6 := by rw [hq, ← pow_mul]; ring_nf
  have e2 : (2 ^ (2 * m)) ^ 2 = q ^ 4 := by rw [hq, ← pow_mul, ← pow_mul]; ring_nf
  have e3 : (2 ^ (2 * m)) ^ 3 = q ^ 6 := by rw [hq, ← pow_mul, ← pow_mul]; ring_nf
  rw [e1, e2, e3]
  have h1 : ∀ k, 1 ≤ q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  zify [h1 2, h1 4, h1 6]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq2
  set x : ℤ := (q : ℤ)
  have hx2 : 4 ≤ x ^ 2 := by nlinarith
  have hA : 0 < x ^ 6 := by positivity
  have hB : 0 < x ^ 6 - 1 := by nlinarith
  have hC : 0 < x ^ 2 - 1 := by linarith
  have key : x ^ 6 * ((x ^ 4 - 1) * (x ^ 6 - 1)) - 3 * (x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1)) =
      x ^ 6 * (x ^ 6 - 1) * (x ^ 2 - 1) * (x ^ 2 - 2) := by ring
  have hD : 0 < x ^ 2 - 2 := by linarith
  have := mul_pos (mul_pos (mul_pos hA hB) hC) hD
  linarith

end CFSG.RankThree.PartTwo.Sec21.Item21LateProof
