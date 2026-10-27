module

import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofList
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofFinal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

theorem card_sp4_ne_ordG2_aux {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 3) ^ 4 * (((q ^ 3) ^ 2 - 1) * ((q ^ 3) ^ 4 - 1)) ≠
      (q ^ 2) ^ 6 * ((q ^ 2) ^ 6 - 1) * ((q ^ 2) ^ 2 - 1) := by
  intro h
  have h1 : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ (q ^ 3) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  have h3 : 1 ≤ (q ^ 2) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have h4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2, h3, h4] at h
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hprod : (q : ℤ) ^ 12 * ((q : ℤ) ^ 12 - 1) * ((q : ℤ) ^ 6 - (q : ℤ) ^ 4) = 0 := by
    linear_combination h
  have hne1 : (q : ℤ) ^ 12 ≠ 0 := by positivity
  have hne2 : (q : ℤ) ^ 12 - 1 ≠ 0 := by
    have : (2 : ℤ) ^ 12 ≤ (q : ℤ) ^ 12 := pow_le_pow_left₀ (by norm_num) hq' 12
    linarith
  have hne3 : (q : ℤ) ^ 6 - (q : ℤ) ^ 4 ≠ 0 := by
    have : (q : ℤ) ^ 6 - (q : ℤ) ^ 4 = (q : ℤ) ^ 4 * ((q : ℤ) ^ 2 - 1) := by ring
    rw [this]
    have : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
    positivity
  rcases mul_eq_zero.mp hprod with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hne1 h''
    · exact hne2 h''
  · exact hne3 h'

theorem card_sp4_ne_ordG2 {n m : ℕ} (hm : 1 ≤ m) (h : n * 4 = m * 6) :
    2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠ CFSG.Open.ordG2 (2 ^ m) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  obtain rfl : n = 3 * k := by omega
  have hk : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : 2 ^ (3 * k * 4) = ((2 ^ k) ^ 3) ^ 4 := by rw [← pow_mul, ← pow_mul]; ring_nf
  have e2 : (2 : ℕ) ^ (3 * k) = (2 ^ k) ^ 3 := by rw [← pow_mul]; ring_nf
  have e3 : (2 : ℕ) ^ (2 * k) = (2 ^ k) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [e1, e2, e3, CFSG.Open.ordG2]
  exact card_sp4_ne_ordG2_aux hk

theorem card_sp4_ne_ordD4_aux {r : ℕ} (hr : 2 ≤ r) :
    (r ^ 3) ^ 4 * (((r ^ 3) ^ 2 - 1) * ((r ^ 3) ^ 4 - 1)) ≠
      r ^ 12 * (r ^ 8 + r ^ 4 + 1) * (r ^ 6 - 1) * (r ^ 2 - 1) := by
  intro h
  have h1 : 1 ≤ (r ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ (r ^ 3) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  have h3 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have h4 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2, h3, h4] at h
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hprod : (r : ℤ) ^ 12 * ((r : ℤ) ^ 6 - 1) * ((r : ℤ) ^ 8 + (r : ℤ) ^ 4 + 1) *
      ((r : ℤ) ^ 4 - (r : ℤ) ^ 2) = 0 := by
    linear_combination h
  have hne1 : (r : ℤ) ^ 12 ≠ 0 := by positivity
  have hne2 : (r : ℤ) ^ 6 - 1 ≠ 0 := by
    have : (2 : ℤ) ^ 6 ≤ (r : ℤ) ^ 6 := pow_le_pow_left₀ (by norm_num) hr' 6
    linarith
  have hne3 : (r : ℤ) ^ 8 + (r : ℤ) ^ 4 + 1 ≠ 0 := by positivity
  have hne4 : (r : ℤ) ^ 4 - (r : ℤ) ^ 2 ≠ 0 := by
    have : (r : ℤ) ^ 4 - (r : ℤ) ^ 2 = (r : ℤ) ^ 2 * ((r : ℤ) ^ 2 - 1) := by ring
    rw [this]
    have : (0 : ℤ) < (r : ℤ) ^ 2 - 1 := by nlinarith
    positivity
  rcases mul_eq_zero.mp hprod with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · rcases mul_eq_zero.mp h'' with h''' | h'''
      · exact hne1 h'''
      · exact hne2 h'''
    · exact hne3 h''
  · exact hne4 h'

theorem card_sp4_ne_ordD4 {n m : ℕ} (hm : 1 ≤ m) (h : n * 4 = m * 12) :
    2 ^ (n * 4) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) ≠
      CFSG.Open.ordTrialityD4 (2 ^ m) := by
  obtain rfl : n = 3 * m := by omega
  have hr : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have e1 : 2 ^ (3 * m * 4) = ((2 ^ m) ^ 3) ^ 4 := by rw [← pow_mul, ← pow_mul]; ring_nf
  have e2 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := by rw [← pow_mul]; ring_nf
  rw [e1, e2, CFSG.Open.ordTrialityD4]
  exact card_sp4_ne_ordD4_aux hr

theorem card_su4_ne_ordD4_aux {r : ℕ} (hr : 2 ≤ r) :
    (r ^ 2) ^ 6 * (((r ^ 2) ^ 2 - 1) * ((r ^ 2) ^ 3 + 1) * ((r ^ 2) ^ 4 - 1)) ≠
      r ^ 12 * (r ^ 8 + r ^ 4 + 1) * (r ^ 6 - 1) * (r ^ 2 - 1) := by
  intro h
  have h1 : 1 ≤ (r ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have h2 : 1 ≤ (r ^ 2) ^ 4 := Nat.one_le_pow _ _ (by positivity)
  have h3 : 1 ≤ r ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have h4 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by positivity)
  zify [h1, h2, h3, h4] at h
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hdiff : (r : ℤ) ^ 12 * ((r : ℤ) ^ 2 - 1) * ((r : ℤ) ^ 2 *
      ((r : ℤ) ^ 14 + (r : ℤ) ^ 6 + (r : ℤ) ^ 2 - 2 * (r : ℤ) ^ 4 - 1)) = 0 := by
    linear_combination h
  have hne1 : (r : ℤ) ^ 12 ≠ 0 := by positivity
  have hne2 : (r : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hne3 : (r : ℤ) ^ 2 * ((r : ℤ) ^ 14 + (r : ℤ) ^ 6 + (r : ℤ) ^ 2 - 2 * (r : ℤ) ^ 4 - 1) ≠
      0 := by
    have hr4 : (16 : ℤ) ≤ (r : ℤ) ^ 4 := by
      have : (2 : ℤ) ^ 4 ≤ (r : ℤ) ^ 4 := pow_le_pow_left₀ (by norm_num) hr' 4
      linarith
    have hr14 : (r : ℤ) ^ 4 * (r : ℤ) ^ 4 ≤ (r : ℤ) ^ 14 := by
      have : (r : ℤ) ^ 14 = (r : ℤ) ^ 4 * (r : ℤ) ^ 4 * (r : ℤ) ^ 6 := by ring
      rw [this]
      have : (1 : ℤ) ≤ (r : ℤ) ^ 6 := one_le_pow₀ (by linarith)
      nlinarith
    have : (0 : ℤ) < (r : ℤ) ^ 14 + (r : ℤ) ^ 6 + (r : ℤ) ^ 2 - 2 * (r : ℤ) ^ 4 - 1 := by
      nlinarith [sq_nonneg (r : ℤ)]
    positivity
  rcases mul_eq_zero.mp hdiff with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hne1 h''
    · exact hne2 h''
  · exact hne3 h'

theorem card_su4_ne_ordD4 {n m : ℕ} (hm : 1 ≤ m) (h : n * 6 = m * 12) :
    Nat.card (projSU 4 2 n) ≠ CFSG.Open.ordTrialityD4 (2 ^ m) := by
  obtain rfl : n = 2 * m := by omega
  have hr : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [card_projSU le_rfl (by omega), ordTwistedA_three_eq (by omega), CFSG.Open.ordTrialityD4,
    show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 by rw [← pow_mul]; ring_nf]
  exact card_su4_ne_ordD4_aux hr

variable {G : Type} [Group G]

section Orders


theorem card_lBar_ne_of_isList218_of [Finite G] {L : Subgroup G} (hL : IsList218 L) {N : ℕ}
    (hM24 : N ≠ 244823040) (hHe : N ≠ 4030387200) (hJ2 : N ≠ 604800)
    (hRu : N ≠ 145926144000) (hJ4 : N ≠ 86775571046077562880)
    (hG2 : ∀ m, 1 ≤ m → CFSG.Open.ordG2 (2 ^ m) ≠ N)
    (hD4 : ∀ m, 1 ≤ m → CFSG.Open.ordTrialityD4 (2 ^ m) ≠ N) :
    Nat.card (lBar L) ≠ N := by
  intro hc
  rcases hL with e | e | e | e | e | ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.Mathieu.card_M24] at hc
    exact hM24 hc.symm
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.He.card_He] at hc
    exact hHe hc.symm
  · rw [Nat.card_congr e.some.toEquiv, KFacts.KS14.card_nativeJ2] at hc
    exact hJ2 hc.symm
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.Ru.card_Ru] at hc
    exact hRu hc.symm
  · rw [Nat.card_congr e.some.toEquiv, Sporadic.J4.card_J4] at hc
    exact hJ4 hc.symm
  · exact hG2 m hm.1.2.1 ((Timmesfeld.card_chevalleyExceptionalModel_two hm).symm.trans hc)
  · exact hD4 m hm.1.2.1 ((Timmesfeld.card_chevalleyExceptionalModel_two hm).symm.trans hc)

theorem card_lBar_ne_of_padic [Finite G] {L : Subgroup G} (hL : IsList218 L) {N k x : ℕ}
    (hN : N = 2 ^ k * x) (hx : Odd x) (hk : ∀ m, 1 ≤ m → m * 6 = k → CFSG.Open.ordG2 (2 ^ m) ≠ N)
    (hk12 : ∀ m, 1 ≤ m → m * 12 ≠ k)
    (hM24 : N ≠ 244823040) (hHe : N ≠ 4030387200) (hJ2 : N ≠ 604800)
    (hRu : N ≠ 145926144000) (hJ4 : N ≠ 86775571046077562880) :
    Nat.card (lBar L) ≠ N := by
  have hvN : padicValNat 2 N = k := by rw [hN, padicValNat_two_pow_mul_odd hx]
  refine card_lBar_ne_of_isList218_of hL hM24 hHe hJ2 hRu hJ4 (fun m hm h => ?_)
    (fun m hm h => ?_)
  · have hv := Item218Proof.padicValNat_ordG2 hm
    rw [h, hvN] at hv
    exact hk m hm hv.symm h
  · have hv := Item218Proof.padicValNat_ordTrialityD4 hm
    rw [h, hvN] at hv
    exact hk12 m hm hv.symm

theorem starOf_cases_of_isList218 [Finite G] (h211 : Item211) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) :
    ((Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.He) ∨
        Nonempty (lBar L ≃* NativeSporadic.Ru) ∨ Nonempty (lBar L ≃* NativeSporadic.J4)) ∧
      (Nonempty (starOf A L ≃* DihedralGroup 6) ∨
        Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3)))) ∨
    ((∃ n : ℕ, 0 < n ∧ Even n ∧ (ChevalleyExceptionalModel (lBar L) .G2 2 n ∨
        ChevalleyExceptionalModel (lBar L) .trialityD4 2 n)) ∧
      Nonempty (starOf A L ≃* DihedralGroup 6)) ∨
    (Nonempty (lBar L ≃* NativeSporadic.J2) ∧ Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) := by
  have h27 := Item2113Proof.card_eq_of_isList218 h211 hpair hL
  rcases h211 G A E U c L hpair with ⟨-, hT, -⟩ | ⟨hM22, -, -⟩ | ⟨hM23 | hHS, -, -⟩ |
      ⟨hMH, -, hS⟩ | ⟨hJ, -, hS⟩ | ⟨hRJ, -, hS⟩ | ⟨⟨n, hn0, hne, h7⟩, -, -⟩ |
      ⟨hGD, -, hS⟩ | ⟨hSU | hU54, -, -⟩ | ⟨-, h81, -⟩ | ⟨-, h81, -⟩ | ⟨h45 | h5, -, -⟩ |
      ⟨-, h81, -⟩
  ·
    exfalso
    refine card_lBar_ne_of_padic hL (N := 1330560) (k := 7) (x := 10395) (by norm_num) (by decide)
      (fun m _ h => by omega) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_
    rw [Item2113Proof.card_of_isTripleCover hT, KFacts.KS14.card_nativeM22]
  ·
    exfalso
    refine card_lBar_ne_of_padic hL (N := 443520) (k := 7) (x := 3465) (by norm_num) (by decide)
      (fun m _ h => by omega) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_
    rw [Nat.card_congr hM22.some.toEquiv, KFacts.KS14.card_nativeM22]
  ·
    exfalso
    refine card_lBar_ne_of_padic hL (N := 10200960) (k := 7) (x := 79695) (by norm_num) (by decide)
      (fun m _ h => by omega) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_
    rw [Nat.card_congr hM23.some.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  ·
    exfalso
    refine card_lBar_ne_of_padic hL (N := 44352000) (k := 9) (x := 86625) (by norm_num) (by decide)
      (fun m _ h => by omega) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_
    rw [Nat.card_congr hHS.some.toEquiv, CFSG.Sporadic.HS.card_HS]
  ·
    left
    refine ⟨hMH.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)), hS⟩
  ·
    exact Or.inr (Or.inr ⟨hJ, hS⟩)
  ·
    left
    refine ⟨hRJ.elim (fun h => Or.inr (Or.inr (Or.inl h))) (fun h => Or.inr (Or.inr (Or.inr h))),
      Or.inr hS⟩
  ·
    exact (Item218Res2Proof.not_isList218_of_lThree hL hn0 hne
      (h7.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))).elim
  ·
    exact Or.inr (Or.inl ⟨hGD, hS⟩)
  ·
    exfalso
    obtain ⟨n, hn0, hne, hSp | hU⟩ := hSU
    · have hn1 : 1 ≤ n := hn0
      have hc := Sec19.Step1911Proof.card_projSp_two hn1
      have hodd : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) :=
        (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
          (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
      have hv : padicValNat 2 (Nat.card (projSp 2 (GaloisField 2 n))) = n * 4 := by
        rw [hc, padicValNat_two_pow_mul_odd hodd]
      have hsp : ∀ M : ℕ, padicValNat 2 M ≠ n * 4 →
          Nat.card (projSp 2 (GaloisField 2 n)) ≠ M := fun M hM h => hM (h ▸ hv)
      refine card_lBar_ne_of_isList218_of hL ?_ ?_ ?_ ?_ ?_ (fun m hm h => ?_)
        (fun m hm h => ?_) (Nat.card_congr hSp.some.toEquiv)
      · refine hsp _ ?_
        rw [show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsp _ ?_
        rw [show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsp _ ?_
        rw [show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num, padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsp _ ?_
        rw [show (145926144000 : ℕ) = 2 ^ 14 * 8906625 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsp _ ?_
        rw [show (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · have hvm := Item218Proof.padicValNat_ordG2 hm
        rw [h, hv] at hvm
        exact card_sp4_ne_ordG2 hm hvm (hc.symm.trans h.symm)
      · have hvm := Item218Proof.padicValNat_ordTrialityD4 hm
        rw [h, hv] at hvm
        exact card_sp4_ne_ordD4 hm hvm (hc.symm.trans h.symm)
    · have hn1 : 1 ≤ n := hn0
      have hv := Item218Proof.padicValNat_card_projSU_four hn1
      have hsu : ∀ M : ℕ, padicValNat 2 M ≠ n * 6 →
          Nat.card (projSU 4 2 n) ≠ M := fun M hM h => hM (h ▸ hv)
      refine card_lBar_ne_of_isList218_of hL ?_ ?_ ?_ ?_ ?_ (fun m hm h => ?_)
        (fun m hm h => ?_) (Nat.card_congr hU.some.toEquiv)
      · refine hsu _ ?_
        rw [show (244823040 : ℕ) = 2 ^ 10 * 239085 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsu _ ?_
        rw [show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsu _ ?_
        rw [show (604800 : ℕ) = 2 ^ 7 * 4725 by norm_num, padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsu _ ?_
        rw [show (145926144000 : ℕ) = 2 ^ 14 * 8906625 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · refine hsu _ ?_
        rw [show (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 by norm_num,
          padicValNat_two_pow_mul_odd (by decide)]
        omega
      · have hvm := Item218Proof.padicValNat_ordG2 hm
        rw [h, hv] at hvm
        obtain rfl : m = n := by omega
        exact Item218Proof.ordG2_ne_card_projSU_four hm h
      · have hvm := Item218Proof.padicValNat_ordTrialityD4 hm
        rw [h, hv] at hvm
        exact card_su4_ne_ordD4 hm hvm h.symm
  ·
    exfalso
    refine card_lBar_ne_of_padic hL (N := 53443952640000) (k := 20) (x := 50968125) (by norm_num)
      (by decide)
      (fun m _ h => by omega) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ?_
    rw [Nat.card_congr hU54.some.toEquiv, Sec4.Item434SmallTwoOther.U54.card_U54]
    norm_num
  · rw [h27] at h81
    norm_num at h81
  · rw [h27] at h81
    norm_num at h81
  ·
    exfalso
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h45).1 rfl
    rw [show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide] at hc
    refine card_lBar_ne_of_padic hL (N := 20160) (k := 6) (x := 315) (by norm_num) (by decide)
      (fun m _ h => ?_) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hc
    obtain rfl : m = 1 := by omega
    decide
  ·
    exfalso
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h5).1 rfl
    rw [show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide] at hc
    exact card_lBar_ne_of_padic hL (N := 9999360) (k := 10) (x := 9765) (by norm_num) (by decide)
      (fun m _ h => by omega) (fun m _ => by omega) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hc
  · rw [h27] at h81
    norm_num at h81

theorem not_dvd_card_of_sporadic [Finite G] {L : Subgroup G}
    (hL : Nonempty (lBar L ≃* NativeSporadic.M24) ∨ Nonempty (lBar L ≃* NativeSporadic.He) ∨
      Nonempty (lBar L ≃* NativeSporadic.J2) ∨ Nonempty (lBar L ≃* NativeSporadic.Ru) ∨
      Nonempty (lBar L ≃* NativeSporadic.J4)) :
    ¬ 81 ∣ Nat.card L := by
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    three_not_dvd_card_aschbacherSolvableCore
  have hcop : Nat.Coprime 81 (Nat.card (aschbacherSolvableCore 3 L)) := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ)
  have hcard : Nat.card L = Nat.card (lBar L) * Nat.card (aschbacherSolvableCore 3 L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hbar : ¬ 81 ∣ Nat.card (lBar L) := by
    rcases hL with e | e | e | e | e
    · rw [Nat.card_congr e.some.toEquiv, Sporadic.Mathieu.card_M24]; norm_num
    · rw [Nat.card_congr e.some.toEquiv, Sporadic.He.card_He]; norm_num
    · rw [Nat.card_congr e.some.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num
    · rw [Nat.card_congr e.some.toEquiv, Sporadic.Ru.card_Ru]; norm_num
    · rw [Nat.card_congr e.some.toEquiv, Sporadic.J4.card_J4]; norm_num
  rw [hcard]
  exact fun h => hbar (hcop.dvd_of_dvd_mul_right h)

end Orders

theorem isSylowOf_of_card [Finite G] {L R : Subgroup G} (hRL : R ≤ L) (hR : Nat.card R = 27)
    (h81 : ¬ 81 ∣ Nat.card L) : CFSG.ABGLocalTools.IsSylowOf 3 R L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRL' : Nat.card (R.subgroupOf L) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv, hR]
  have h27 : 3 ^ 3 ∣ Nat.card L := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hRL']
    exact Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hle : 3 ≤ (Nat.card L).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h27
  have hlt : ¬ 4 ≤ (Nat.card L).factorization 3 := fun h =>
    h81 (by rw [show (81 : ℕ) = 3 ^ 4 by norm_num]
            exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mpr h)
  have hf : (Nat.card L).factorization 3 = 3 := by omega
  refine ⟨Sylow.ofCard (R.subgroupOf L) (by rw [hRL', hf]; norm_num), ?_⟩
  rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_of_le_left hRL]

end CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof
