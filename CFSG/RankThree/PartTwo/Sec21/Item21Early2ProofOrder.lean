module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

namespace Item21Early2Proof

theorem lt_ordG2 {q : ℕ} (hq : 4 ≤ q) : 5616 < CFSG.Open.ordG2 q := by
  unfold CFSG.Open.ordG2
  have h1 : 4096 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  have h2 : 16 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have h3 : 1 ≤ q ^ 6 - 1 := by omega
  have h4 : 15 ≤ q ^ 2 - 1 := by omega
  calc 5616 < 4096 * 1 * 15 := by norm_num
    _ ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4

theorem lt_ordTrialityD4 {q : ℕ} (hq : 4 ≤ q) : 5616 < CFSG.Open.ordTrialityD4 q := by
  unfold CFSG.Open.ordTrialityD4
  have h1 : 4 ^ 12 ≤ q ^ 12 := Nat.pow_le_pow_left hq 12
  have h2 : 16 ≤ q ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
  have h6 : 4096 ≤ q ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
  have h3 : 1 ≤ q ^ 8 + q ^ 4 + 1 := by omega
  have h4 : 1 ≤ q ^ 6 - 1 := by omega
  have h5 : 1 ≤ q ^ 2 - 1 := by omega
  calc 5616 < 4 ^ 12 * 1 * 1 * 1 := by norm_num
    _ ≤ q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4) h5

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)

theorem lt_card_of_bar211Quot
    {Y : Type} [Group Y] (h : Bar211Quot Y) :
    5616 < Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Bar211Quot at h
  rcases h with h | h | h | h | h | h | h | h | h |
      ⟨n, hn, he, h⟩ | ⟨n, hn, he, hG | hD⟩ | ⟨n, hn, he, h⟩ | ⟨n, hn, h⟩ | h |
      h | h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeM22]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.m23_card]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.He.card_He]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J4.card_J4]; norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]; norm_num
  ·
    obtain ⟨e⟩ := h
    have h20 := Sec13.le_card_of_isoLThreePi (Y := Y) (p := 2) (e := n) (by omega)
      (Or.inl ⟨two_pow_mod_three_of_even he, ⟨e⟩⟩)
      (lt_of_lt_of_le (by norm_num) (four_le_two_pow hn))
    omega
  ·
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG]
    exact lt_ordG2 (four_le_two_pow hn)
  ·
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD]
    exact lt_ordTrialityD4 (four_le_two_pow hn)
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSp_two (by omega)]
    have hq := four_le_two_pow hn
    have h1 : 2 ^ 8 ≤ 2 ^ (n * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
    have h3 : 256 ≤ (2 ^ n) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 4)
    calc 5616 < 2 ^ 8 * (15 * 255) := by norm_num
      _ ≤ 2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    have := Item223PrintProof.card_projSU_four_ge hn
    omega
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sec4.Item434SmallTwoOther.U54.card_U54]; norm_num
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) le_rfl,
      show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide]
    norm_num
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) le_rfl,
      show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
    norm_num
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sec6.BThreeCensus.card_projSp_three_two]; norm_num

end Item21Early2Proof

open Item21Early2Proof

theorem ks213Order :
    KS213Order :=
  fun _ _ _ hX => lt_card_of_bar211Quot (bar211Quot_of_isBar211 hX)

end CFSG.RankThree.PartTwo.Sec21
