module

public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofFour
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofOrder
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.Sec21.Item22Tools
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

@[expose] def Item214UnitaryOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
      ¬ ∃ U' ∈ fourGroupsMinus E, U' ≤ L

namespace Item21Early2Proof

theorem card_projSU_four_one : Nat.card (projSU 4 2 1) = 25920 :=
  CFSG.PGLModel.card_projSU_four_two

theorem card_ne_of_bar211Quot
    {Y : Type} [Group Y] (h : Bar211Quot Y) :
    Nat.card Y ≠ 25920 := by
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
    intro hY
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega), ← Nat.card_congr e.toEquiv, hY] at hc
    have hg : Nat.gcd 3 (2 ^ n - 1) = 3 :=
      Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero (by
        have := two_pow_mod_three_of_even he
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega))
    rw [hg] at hc
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      norm_num at hc
    · have hq : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
      have h1 : 512 ≤ (2 ^ n) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
      have h2 : 64 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
      have h3 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
      have h4 : 511 ≤ (2 ^ n) ^ 3 - 1 := by omega
      have : 512 * (63 * 511) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
      omega
  ·
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG]
    have hq : 4 ≤ 2 ^ n := four_le_two_pow hn
    have hlt : 25920 < CFSG.Open.ordG2 (2 ^ n) := by
      unfold CFSG.Open.ordG2
      have h1 : 4096 ≤ (2 ^ n) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
      have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
      have h3 : 4095 ≤ (2 ^ n) ^ 6 - 1 := by omega
      have h4 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
      calc 25920 < 4096 * 4095 * 15 := by norm_num
        _ ≤ (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4
    exact Nat.ne_of_gt hlt
  ·
    rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD]
    have hq : 4 ≤ 2 ^ n := four_le_two_pow hn
    have hlt : 25920 < CFSG.Open.ordTrialityD4 (2 ^ n) := by
      unfold CFSG.Open.ordTrialityD4
      have h1 : 4 ^ 12 ≤ (2 ^ n) ^ 12 := Nat.pow_le_pow_left hq 12
      have h6 : 4096 ≤ (2 ^ n) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
      have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
      have h3 : 1 ≤ (2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1 := by omega
      have h4 : 1 ≤ (2 ^ n) ^ 6 - 1 := by omega
      have h5 : 1 ≤ (2 ^ n) ^ 2 - 1 := by omega
      calc 25920 < 4 ^ 12 * 1 * 1 * 1 := by norm_num
        _ ≤ (2 ^ n) ^ 12 * ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1) * ((2 ^ n) ^ 6 - 1) *
            ((2 ^ n) ^ 2 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h4) h5
    exact Nat.ne_of_gt hlt
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Sec19.Step1911Proof.card_projSp_two (by omega)]
    have hq := four_le_two_pow hn
    have h1 : 2 ^ 8 ≤ 2 ^ (n * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
    have h3 : 256 ≤ (2 ^ n) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 4)
    have : 2 ^ 8 * (15 * 255) ≤ 2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))
    omega
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, card_projSU le_rfl (by omega), ordTwistedA_three_eq (by omega)]
    have hq := four_le_two_pow hn
    have h1 : 4096 ≤ (2 ^ n) ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 6)
    have h2 : 16 ≤ (2 ^ n) ^ 2 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 2)
    have h3 : 64 ≤ (2 ^ n) ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 3)
    have h4 : 256 ≤ (2 ^ n) ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 4)
    have : 4096 * (15 * 65 * 255) ≤ (2 ^ n) ^ 6 *
        (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
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

open Item21EarlyProof Item21Early2Proof

theorem item214Unitary_of
    (h211 : Item211) (hOdd : Item214UnitaryOdd) :
    Item214Unitary := by
  intro G _ _ A E U c L hpair ⟨n, hno, hn⟩
  rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · exact hOdd G A E U c L hpair ⟨n, hn1, hno, hn⟩
  · exfalso
    obtain rfl : n = 1 := by obtain ⟨k, rfl⟩ := hno; omega
    obtain ⟨e⟩ := hn
    have : IsSimpleGroup (projSU 4 2 1) := isSimpleGroup_projSU le_rfl le_rfl
    have : IsSimpleGroup L := e.isSimpleGroup
    have hL : Nat.card L = 25920 := by rw [Nat.card_congr e.toEquiv, card_projSU_four_one]
    have hX : IsBar211 (lBar L) := isBar211_of_case211 (h211 G A E U c L hpair)
    obtain ⟨hTs, -, -, -⟩ := solvable_prime_complement_core_characterization (H := L)
      Nat.prime_three
    have hZL : Subgroup.center L = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_prime (by
      rw [hL]; norm_num)
    have hT : aschbacherSolvableCore 3 L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 L) with h | h
      · exact h
      · exfalso
        rw [h] at hTs
        have hsol : Group.IsSolvable L :=
          Group.isSolvable_of_surjective (f := (⊤ : Subgroup L).subtype)
            (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
        have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hsol
        have htop : Subgroup.center L = ⊤ := by
          rw [eq_top_iff]
          intro x _
          rw [Subgroup.mem_center_iff]
          intro y
          exact hcomm y x
        have h1 := congrArg (fun H : Subgroup L => Nat.card H) (hZL.symm.trans htop)
        simp only [Subgroup.card_bot, Subgroup.card_top, hL] at h1
        omega
    let eT : lBar L ≃* L := (QuotientGroup.quotientMulEquivOfEq hT).trans QuotientGroup.quotientBot
    have : IsSimpleGroup (lBar L) := eT.isSimpleGroup
    have hZ : Subgroup.center (lBar L) = ⊥ := center_eq_bot_of_isSimpleGroup_of_not_prime (by
      rw [Nat.card_congr eT.toEquiv, hL]; norm_num)
    have hcard : Nat.card (lBar L ⧸ Subgroup.center (lBar L)) = 25920 := by
      rw [Nat.card_congr ((quotCenterEquivOfBot hZ).trans eT).toEquiv, hL]
    exact card_ne_of_bar211Quot (bar211Quot_of_isBar211 hX) hcard

end CFSG.RankThree.PartTwo.Sec21
