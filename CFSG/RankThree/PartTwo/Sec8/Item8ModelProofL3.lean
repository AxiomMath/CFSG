module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofL3
public import CFSG.RankThree.PartTwo.Sec8.Item82Res2ProofKinds
public import CFSG.RankThree.PartTwo.KFacts.K71IdentPSU3
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL34
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofTransport
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.PartTwo.Census.Suzuki
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCross

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)
open Matrix

namespace Item8ModelProof

theorem card_projSL_three_galois {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (projSL 3 (GaloisField 2 n)) = ordA 2 (2 ^ n) := by
  rw [Nat.card_congr (Sec4.projSLEquivPSLn 3 (GaloisField 2 n)).toEquiv,
    card_psl_eq_ordA (by norm_num) (GaloisField.card 2 n (by omega))]

theorem padicValNat_ordA_two {n : ℕ} (hn : 1 ≤ n) : padicValNat 2 (ordA 2 (2 ^ n)) = 3 * n := by
  obtain ⟨s, hs, hseq⟩ := (profA2 hn).two
  rw [hseq, padicValNat.mul (by positivity) hs.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hs.not_two_dvd_nat, add_zero]
  ring

theorem ordA_two_le (q : ℕ) : ordA 2 q ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h3 : 2 * (2 + 1) / 2 = 3 := by norm_num
  rw [ordA, h3, show Finset.Icc 2 (2 + 1) = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
  exact Nat.div_le_self _ _

theorem ordA_two_lt {n : ℕ} (hn : 1 ≤ n) : ordA 2 (2 ^ n) < 2 ^ (8 * n) := by
  set q := 2 ^ n with hq
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : q ^ 2 - 1 < q ^ 2 := by have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega); omega
  have h3 : q ^ 3 - 1 < q ^ 3 := by have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega); omega
  calc ordA 2 q ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := ordA_two_le q
    _ < q ^ 3 * (q ^ 2 * q ^ 3) := by
        apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
        calc (q ^ 2 - 1) * (q ^ 3 - 1) ≤ (q ^ 2 - 1) * q ^ 3 := Nat.mul_le_mul_left _ h3.le
          _ < q ^ 2 * q ^ 3 := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
    _ = 2 ^ (8 * n) := by rw [hq, ← pow_add, ← pow_add, ← pow_mul]; ring_nf

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨j, rfl⟩ := hn
  have h : 2 ^ (j + j) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have : 1 ≤ 2 ^ (j + j) := Nat.one_le_two_pow
  omega

end Item8ModelProof

open Item8ModelProof


namespace Item8ModelProof

theorem not_oddCharStdModel_of_card {X : Type} [Group X] (h6 : 6 ≤ padicValNat 2 (Nat.card X))
    (hlt : Nat.card X ^ 3 < 2 ^ (8 * padicValNat 2 (Nat.card X)))
    (h25920 : Nat.card X ≠ 25920) : ¬ OddCharStdModel X := by
  rintro ⟨K, _, _, hK2, hX⟩
  have key : ∀ {Y : Type} [Group Y], Nonempty (X ≃* Y) →
      (6 ≤ padicValNat 2 (Nat.card Y) → 2 ^ (8 * padicValNat 2 (Nat.card Y)) ≤ Nat.card Y ^ 3) →
        False := by
    rintro Y _ ⟨e'⟩ hY
    rw [← Nat.card_congr e'.toEquiv] at hY
    have := hY h6
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
    · obtain ⟨rfl, hK3⟩ := h23
      obtain ⟨e'⟩ := hY
      have hN : Nat.card (StatedProj (StatedSp 2 K)) = 25920 := by
        rw [hK3, show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)] at hc
        norm_num at hc
        omega
      exact h25920 ((Nat.card_congr e'.toEquiv).trans hN)
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

theorem not_oddCharStdModel_of_mulEquiv_projSL {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* projSL 3 (GaloisField 2 n)) : ¬ OddCharStdModel X := by
  have hcard : Nat.card X = ordA 2 (2 ^ n) :=
    (Nat.card_congr e.toEquiv).trans (card_projSL_three_galois (by omega))
  have hv := padicValNat_ordA_two (n := n) (by omega)
  refine not_oddCharStdModel_of_card (by rw [hcard, hv]; omega) ?_ ?_
  · rw [hcard, hv]
    calc ordA 2 (2 ^ n) ^ 3 < (2 ^ (8 * n)) ^ 3 :=
          Nat.pow_lt_pow_left (ordA_two_lt (by omega)) (by norm_num)
      _ = 2 ^ (8 * (3 * n)) := by rw [← pow_mul]; ring_nf
  · intro h
    have h6 : padicValNat 2 25920 = 6 := by
      rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [hcard] at h
    rw [h, h6] at hv
    obtain rfl : n = 2 := by omega
    revert h
    decide

end Item8ModelProof


theorem kF82PSL3EvenModel_holds : KF82PSL3EvenModel := by
  intro G _ _ L x n k hn hn2 hL hx
  obtain ⟨eL⟩ := hL
  have hcardX : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = ordA 2 (2 ^ n) :=
    (Nat.card_congr eL.toEquiv).trans (card_projSL_three_galois (by omega))
  have hM : ∀ {M : Type} [Group M], (L ⧸ aschbacherSolvableCore 3 L ≃* M) →
      Nat.card M = ordA 2 (2 ^ n) := fun e => (Nat.card_congr e.toEquiv).symm.trans hcardX
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    center_eq_bot_of_mulEquiv_fwd (eL.trans (Sec4.projSLEquivProjectiveSL 3 _)).symm
      (Sec21.Item223CensusResProof.center_projectiveSL_three _)
  have hodd := not_oddCharStdModel_of_mulEquiv_projSL hn2 eL
  have h3 : 3 ∣ 2 ^ n - 1 := three_dvd_two_pow_sub_one hn
  cases hx with
  | psl2 K h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [card_psl_eq_ordA (by norm_num) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by norm_num) hf hn2 h1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2, Or.inl ⟨e⟩⟩).elim
  | psl m K hm h =>
    obtain ⟨e, -⟩ := id h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [← Nat.card_congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL m K).toEquiv,
        card_psl_eq_ordA (by omega) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by omega) hf hn2 h1 with ⟨hm3, rfl⟩ | ⟨hm4, rfl, rfl⟩
      · obtain rfl : m = 3 := by omega
        exact ⟨K, inferInstance, inferInstance, hKf, h⟩
      · obtain rfl : m = 4 := by omega
        have : CharP K 2 := ringChar.of_eq hK2
        exact (false_of_mulEquiv_projectiveSL_four eL e).elim
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2, Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩)⟩).elim
  | sl m K hm h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have hZ' : Subgroup.center (SpecialLinearGroup (Fin m) K) = ⊥ :=
        center_eq_bot_of_mulEquiv_fwd e hZ
      have hc1 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin m) K)) = 1 := by
        rw [hZ', Subgroup.card_bot]
      have h1 := hM e
      have h2 : Nat.card (SpecialLinearGroup (Fin m) K) =
          Nat.card (ProjectiveSpecialLinearGroup (Fin m) K) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center (SpecialLinearGroup (Fin m) K)), hc1, mul_one]
      rw [h2, card_psl_eq_ordA (by omega) hKf] at h1
      rcases eq_of_ordA_eq_ordA_two (by omega) hf hn2 h1 with ⟨hm3, rfl⟩ | ⟨hm4, rfl, rfl⟩
      · obtain rfl : m = 3 := by omega
        exact (Sec21.Item223CensusResProof.center_SL_three_ne_bot (by rw [hKf]; exact h3)
          hZ').elim
      · obtain rfl : m = 4 := by omega
        have : CharP K 2 := ringChar.of_eq hK2
        exact (false_of_mulEquiv_SL_four eL e).elim
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩))⟩).elim
  | @psu3 p f K _ hK hq h =>
    obtain ⟨e, -⟩ := id h
    by_cases hp : p = 2
    · subst hp
      have h1 := hM e
      rw [card_unitaryPSU_three_eq hK] at h1
      exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
        hK.one_le h1.symm).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact (hodd ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inl ⟨e⟩⟩))))⟩).elim
  | @su3 p f K _ hK hq h =>
    obtain ⟨e, -, -⟩ := h
    by_cases hp : p = 2
    · subst hp
      have hZ' : Subgroup.center (unitarySU 2 f K 3) = ⊥ := center_eq_bot_of_mulEquiv_fwd e hZ
      by_cases h3' : 3 ∣ 2 ^ f + 1
      · obtain ⟨z, hz, hz1, -⟩ := exists_mem_center_statedSU_ne_one hK h3'
        rw [hZ', Subgroup.mem_bot] at hz
        exact (hz1 hz).elim
      · have hsc : Nat.card (unitaryScalars hK 3) = 1 := by
          rw [card_unitaryScalars hK (by norm_num)]
          exact Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
        have h1 := hM e
        have h2 : Nat.card (unitarySU 2 f K 3) = ordTwistedA 2 (2 ^ f) := by
          rw [← card_unitaryPSU_three_eq hK,
            (unitaryScalars hK 3).card_eq_card_quotient_mul_card_subgroup, hsc, mul_one]
        rw [h2] at h1
        exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (by norm_num) (by omega) le_rfl
          hK.one_le h1.symm).elim
    · have := hK.finite
      have : CharP K p := hK.charP
      exact (hodd ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨p, f, hK, Or.inr ⟨e⟩⟩))))⟩).elim
  | psp r K hr h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · have hr3 : 3 ≤ r := by
        rcases hr with hr | ⟨-, hc⟩
        · exact hr
        · exact (hc hK2).elim
      obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have : CharP K 2 := ringChar.of_eq hK2
      have h1 := hM e
      rw [card_statedProj_statedSp_eq_ordBC hf hKf] at h1
      exact (ordBC_ne_ordA_two hr3 hf (by omega) h1).elim
    · have hr2 : 2 ≤ r := by rcases hr with hr | ⟨rfl, -⟩ <;> omega
      exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr2, ⟨e⟩⟩)))⟩).elim
  | psp4even F h =>
    obtain ⟨e, -⟩ := h
    obtain ⟨f, hf, hFf⟩ := exists_card_eq_two_pow (ringChar.eq F 2)
    have h1 := hM e
    rw [card_statedProj_statedSp_eq_ordBC hf hFf] at h1
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordBC_two (by norm_num) (by omega) hf h1.symm).elim
  | g2 K hK3 hK4 h =>
    obtain ⟨e, -⟩ := h
    by_cases hK2 : ringChar K = 2
    · obtain ⟨f, hf, hKf⟩ := exists_card_eq_two_pow hK2
      have h1 := hM e
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hKf] at h1
      exact (ordG2_ne_ordA_two hf (by omega) h1).elim
    · exact (hodd ⟨K, inferInstance, inferInstance, hK2,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩))))⟩).elim
  | sz a K ha hK h =>
    obtain ⟨e, -⟩ := h
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have h1 := hM e
    rw [Nat.card_congr
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv,
      CFSG.RankThree.PartTwo.Census.card_suzukiMatrixGroup (by omega), suzuki_eq_ordSuzuki] at h1
    exact (ordSuzuki_ne_ordA_two (by omega) (by omega) h1).elim
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, -, -⟩ := h
    have h1 := hM e
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hf hK σ.toRingHom
      hσ] at h1
    exact (ordTrialityD4_ne_ordA_two hf (by omega) h1).elim
  | largeRee a ha K hK h =>
    obtain ⟨e, -⟩ := h
    have h1 := hM e
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).1, ree_native_eq_ordTwistedF4 Nat.one_le_two_pow] at h1
    exact (ordTwistedF4_ne_ordA_two (by omega) (by omega) h1).elim

theorem kF82LThreeWrong_holds : KF82LThreeWrong :=
  kF82LThreeWrong_of kF82PSL3EvenModel_holds

namespace Item82Proof

theorem kF82LThreeModel_holds : KF82LThreeModel := by
  intro G _ _ L x n k hn hn1 hL hx
  have hn2 : 2 ≤ n := by obtain ⟨j, rfl⟩ := hn; omega
  obtain ⟨K, _, _, hK, hkK⟩ := kF82PSL3EvenModel_holds G L x n k hn hn2 hL hx
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 n (by omega)]
  exact inducesKindPSL_of_ringEquiv (FiniteField.ringEquivOfCardEq hcard) 3 hkK

theorem kF82TwoLThreeKinds_holds : KF82TwoLThreeKinds :=
  kF82TwoLThreeKinds_of kF82LThreeModel_holds

end Item82Proof

end CFSG.RankThree.PartTwo.Sec8
