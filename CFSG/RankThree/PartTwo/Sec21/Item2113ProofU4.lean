module

public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofFinal
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofFour
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofList
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

@[expose] def Item2115U4Ten : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → (∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) →
    Nat.card A = 3 ^ 4 → Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) →
      ¬ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

namespace Item2113Proof

theorem card_lThree_ne_uFour {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1)) ≠
      3 * (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))) := by
  intro h
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
  have h6 : 1 ≤ (q ^ 2) ^ 3 := Nat.one_le_pow _ _ h2
  have h4' : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4, h6, h4'] at h
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hprod : (q : ℤ) ^ 6 * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 3 + 1) *
      (((q : ℤ) ^ 3 - 1) - 3 * ((q : ℤ) ^ 2 - 1)) = 0 := by linear_combination h
  have hne1 : (q : ℤ) ^ 6 ≠ 0 := by positivity
  have hne2 : (q : ℤ) ^ 4 - 1 ≠ 0 := by nlinarith [pow_le_pow_left₀ (by norm_num) hq' 4]
  have hne3 : (q : ℤ) ^ 3 + 1 ≠ 0 := by positivity
  have hkey : ((q : ℤ) ^ 3 - 1) - 3 * ((q : ℤ) ^ 2 - 1) = 0 := by
    rcases mul_eq_zero.mp hprod with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h''' | h'''
        · exact absurd h''' hne1
        · exact absurd h''' hne2
      · exact absurd h'' hne3
    · exact h'
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · obtain rfl : q = 2 := by omega
    norm_num at hkey
  · have h3' : (3 : ℤ) ≤ q := by exact_mod_cast h3
    nlinarith [sq_nonneg (q : ℤ)]

theorem card_slThree_ne_uFour {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1)) ≠
      q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
  intro h
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ (q ^ 2) ^ 2 := Nat.one_le_pow _ _ h2
  have h6 : 1 ≤ (q ^ 2) ^ 3 := Nat.one_le_pow _ _ h2
  have h4' : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h4, h6, h4'] at h
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hprod : (q : ℤ) ^ 6 * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 3 + 1) *
      (((q : ℤ) ^ 3 - 1) - ((q : ℤ) ^ 2 - 1)) = 0 := by linear_combination h
  have hne1 : (q : ℤ) ^ 6 ≠ 0 := by positivity
  have hne2 : (q : ℤ) ^ 4 - 1 ≠ 0 := by nlinarith [pow_le_pow_left₀ (by norm_num) hq' 4]
  have hne3 : (q : ℤ) ^ 3 + 1 ≠ 0 := by positivity
  have hkey : ((q : ℤ) ^ 3 - 1) - ((q : ℤ) ^ 2 - 1) = 0 := by
    rcases mul_eq_zero.mp hprod with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h''' | h'''
        · exact absurd h''' hne1
        · exact absurd h''' hne2
      · exact absurd h'' hne3
    · exact h'
  nlinarith [sq_nonneg (q : ℤ)]

variable {G : Type} [Group G]

section Ten


theorem case_ten_of_projSU_four [Finite G] (h211 : Item211) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {n : ℕ} (hno : Odd n) (e : L ≃* projSU 4 2 n) :
    1 < n ∧ Nat.card A = 3 ^ 4 ∧ Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)) := by
  have hn1 : 1 ≤ n := hno.pos
  have hN := Item218Proof.padicValNat_card_projSU_four hn1
  have hM := Item218Proof.card_lBar_of_mulEquiv_projSU_four hn1 e
  have hv : padicValNat 2 (Nat.card (lBar L)) = 0 ∨
      padicValNat 2 (Nat.card (lBar L)) = n * 6 := by
    rcases hM with h | h
    · left
      rw [h, padicValNat_one_right]
    · right
      rw [h, hN]
  have hv2 : ∀ {k x : ℕ}, Odd x → Nat.card (lBar L) = 2 ^ k * x → k = 0 ∨ k = n * 6 := by
    intro k x hx h
    rw [h, padicValNat_two_pow_mul_odd hx] at hv
    exact hv
  obtain ⟨n', hn'⟩ := hno
  rcases h211 G A E U c L hpair with ⟨-, hT, -, -, -⟩ | ⟨f, -, -⟩ | ⟨f | f, -, -⟩ |
      ⟨f | f, -, -⟩ | ⟨f, -, -⟩ | ⟨f | f, -, -⟩ |
      ⟨⟨m, hm0, hme, ⟨f, -⟩ | ⟨f, -⟩⟩, -, -⟩ | ⟨⟨m, hm0, hme, hG | hD⟩, -, -⟩ |
      ⟨⟨m, hm0, hme, f | f⟩ | f, -, -⟩ | ⟨⟨m, hm1, hmo, f⟩, h81, hS4⟩ |
      ⟨h11, -, -⟩ | ⟨h4 | h5, -, -⟩ | ⟨h13, -, -⟩
  ·
    have h := hv2 (k := 7) (x := 10395) (by decide)
      (by rw [card_of_isTripleCover hT, KFacts.KS14.card_nativeM22]; norm_num)
    omega
  · have h := hv2 (k := 7) (x := 3465) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, KFacts.KS14.card_nativeM22]; norm_num)
    omega
  · have h := hv2 (k := 7) (x := 79695) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, CFSG.Sporadic.Schreier.m23_card]; norm_num)
    omega
  · have h := hv2 (k := 9) (x := 86625) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, CFSG.Sporadic.HS.card_HS]; norm_num)
    omega
  · have h := hv2 (k := 10) (x := 239085) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, Sporadic.Mathieu.card_M24]; norm_num)
    omega
  · have h := hv2 (k := 10) (x := 3935925) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, Sporadic.He.card_He]; norm_num)
    omega
  · have h := hv2 (k := 7) (x := 4725) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, KFacts.KS14.card_nativeJ2]; norm_num)
    omega
  · have h := hv2 (k := 14) (x := 8906625) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, Sporadic.Ru.card_Ru]; norm_num)
    omega
  · have h := hv2 (k := 21) (x := 41377816699065) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, Sporadic.J4.card_J4]; norm_num)
    omega
  ·
    have hm1 : 1 ≤ m := hm0
    have hvm := Item218Res2Proof.padicValNat_card_projSL hme hm1
    rw [← Nat.card_congr f.some.toEquiv] at hvm
    have hMN : Nat.card (lBar L) = Nat.card (projSU 4 2 n) := by
      rcases hM with h | h
      · rw [h, padicValNat_one_right] at hvm
        omega
      · exact h
    rcases hv with h | h
    · omega
    · have hm2 : m = 2 * n := by omega
      have hc := Item218Res2Proof.card_projSL_mul_three hme hm1
      rw [← Nat.card_congr f.some.toEquiv, hMN, card_projSU le_rfl hn1, ordTwistedA_three_eq hn1,
        hm2, pow_mul, show (2 ^ 2) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, ← pow_mul, mul_comm]]
        at hc
      exact (card_lThree_ne_uFour (q := 2 ^ n) (Nat.le_self_pow (by omega) 2)
        (by rw [← hc]; ring)).elim
  ·
    have hm1 : 1 ≤ m := hm0
    have hc := Item218Res2Proof.card_SL3 hm1
    rw [← Nat.card_congr f.some.toEquiv] at hc
    have hvm : padicValNat 2 (Nat.card (lBar L)) = 3 * m := by
      rw [hc, Item218Res2Proof.padicValNat_two_pow_cube_mul_odd
        (Item218Res2Proof.odd_sl3Part hm1)]
    have hMN : Nat.card (lBar L) = Nat.card (projSU 4 2 n) := by
      rcases hM with h | h
      · rw [h, padicValNat_one_right] at hvm
        omega
      · exact h
    rcases hv with h | h
    · omega
    · have hm2 : m = 2 * n := by omega
      rw [hMN, card_projSU le_rfl hn1, ordTwistedA_three_eq hn1, hm2, pow_mul,
        show (2 ^ 2) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, ← pow_mul, mul_comm]] at hc
      exact (card_slThree_ne_uFour (q := 2 ^ n) (Nat.le_self_pow (by omega) 2) hc.symm).elim
  ·
    have hm1 : 1 ≤ m := hm0
    have hvm := Item218Proof.padicValNat_ordG2 hm1
    have hc : Nat.card (lBar L) = CFSG.Open.ordG2 (2 ^ m) :=
      Timmesfeld.card_chevalleyExceptionalModel_two hG
    rw [← hc] at hvm
    obtain ⟨k, hk⟩ := hme
    omega
  ·
    have hm1 : 1 ≤ m := hm0
    have hvm := Item218Proof.padicValNat_ordTrialityD4 hm1
    have hc : Nat.card (lBar L) = CFSG.Open.ordTrialityD4 (2 ^ m) :=
      Timmesfeld.card_chevalleyExceptionalModel_two hD
    rw [← hc] at hvm
    omega
  ·
    have hm1 : 1 ≤ m := hm0
    have hodd : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) :=
      (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
        (Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
    have h := hv2 hodd
      (by rw [Nat.card_congr f.some.toEquiv, Sec19.Step1911Proof.card_projSp_two hm1])
    omega
  ·
    have hm1 : 1 ≤ m := hm0
    have hvm := Item218Proof.padicValNat_card_projSU_four hm1
    rw [← Nat.card_congr f.some.toEquiv] at hvm
    obtain ⟨k, hk⟩ := hme
    omega
  ·
    have h := hv2 (k := 20) (x := 50968125) (by decide)
      (by rw [Nat.card_congr f.some.toEquiv, Sec4.Item434SmallTwoOther.U54.card_U54]; norm_num)
    omega
  ·
    have hvm := Item218Proof.padicValNat_card_projSU_four (by omega : 1 ≤ m)
    rw [← Nat.card_congr f.some.toEquiv] at hvm
    exact ⟨by omega, h81, hS4⟩
  ·
    rcases h11 with f | h3
    · have h := hv2 (k := 7) (x := 392445) (by decide)
        (by rw [Nat.card_congr f.some.toEquiv, CFSG.Sporadic.J3.card_J3]; norm_num)
      omega
    · have h := hv2 (k := 7) (x := 1177335) (by decide)
        (by rw [card_of_isTripleCover h3, CFSG.Sporadic.J3.card_J3]; norm_num)
      omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h4).1 rfl
    rw [show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide] at hc
    have h := hv2 (k := 6) (x := 315) (by decide) (by rw [hc]; norm_num)
    obtain rfl : n = 1 := by omega
    rcases hM with h' | h'
    · rw [hc] at h'
      omega
    · rw [hc, Item21Early2Proof.card_projSU_four_one] at h'
      omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h5).1 rfl
    rw [show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide] at hc
    have h := hv2 (k := 10) (x := 9765) (by decide) (by rw [hc]; norm_num)
    omega
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h13).2.2.1 rfl
    rw [show CFSG.Open.ordBC 3 (2 ^ 1) = 1451520 by decide] at hc
    have h := hv2 (k := 9) (x := 2835) (by decide) (by rw [hc]; norm_num)
    omega

theorem item2115U4_of (h211 : Item211) (hT : Item2115U4Ten) : Item2115U4 := by
  intro G _ _ A E U c L hpair ⟨n, hno, ⟨e⟩⟩
  obtain ⟨hn, h81, hS4⟩ := case_ten_of_projSU_four h211 hpair hno e
  exact hT G A E U c L hpair ⟨n, hn, hno, ⟨e⟩⟩ h81 hS4

end Ten

end Item2113Proof

end CFSG.RankThree.PartTwo.Sec21
