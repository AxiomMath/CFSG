module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

structure uc22p20vExclRes : Prop where
  lin : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ m n : ℕ, (m = 5 ∨ m = 6 ∨ m = 7) → 2 < n → Odd n → LieModel (K ⧸ center K) .PSL m 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → uc22p20oBorelWit K p 2
  unitary : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (center K)) →
    ∀ m n : ℕ, (m = 5 ∨ m = 6 ∨ m = 7) → 2 < n → Even n → LieModel (K ⧸ center K) .PSU m 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 → p ≠ 5 → uc22p20oBorelWit K p 2
  u54 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    center K ≠ ⊥ → LieModel (K ⧸ center K) .PSU 5 2 2 → uc22p20oBorelWit K 5 2
  e : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    center K ≠ ⊥ → ∀ n : ℕ, 2 < n →
    (LieModel (K ⧸ center K) .E6 0 2 n ∨ LieModel (K ⧸ center K) .twistedE6 0 2 n) →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → p ≠ 3 → uc22p20oBorelWit K p 4

structure uc22p20vTwoRes : Prop where
  lin3 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ n : ℕ, 2 < n → LieModel (K ⧸ center K) .PSL 3 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → p ≠ 3 → uc22p20oBorelWit K p 1
  unitary3 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (center K)) →
    ∀ n : ℕ, 2 < n → LieModel (K ⧸ center K) .PSU 3 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 → p ≠ 3 → uc22p20oBorelWit K p 1
  d4 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ n : ℕ, LieModel (K ⧸ center K) .trialityD4 0 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → uc22p20oBorelWit K p 2
  f4 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    ∀ n : ℕ, LieModel (K ⧸ center K) .twistedF4 0 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 → uc22p20oBorelWit K p 2
  d4two : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → Odd (Nat.card (center K)) →
    LieModel (K ⧸ center K) .trialityD4 0 2 1 → uc22p20oRankWit K 3 2

section Witnesses

variable {K : Type} [Group K] [Finite K]

theorem uc22p20v_borelWit_mono {p k j : ℕ} (hp : p.Prime) (h : uc22p20oBorelWit K p k) (hj : j ≤ k) :
    uc22p20oBorelWit K p j := by
  intro P
  obtain ⟨F, hFP, hF, hcard⟩ := h P
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p (n := j)
    (by rw [hcard]; exact pow_dvd_pow p hj)
  refine ⟨F'.map F.subtype, (Subgroup.map_subtype_le F').trans hFP,
    CFSG.Open.IsElemAbelian.mono hF (Subgroup.map_subtype_le F'), ?_⟩
  rw [Subgroup.card_map_of_injective F.subtype_injective, hF']

theorem uc22p20v_rankWit_of_borelWit {p k : ℕ} (h : uc22p20oBorelWit K p k) :
    uc22p20oRankWit K p k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨F, -, hF, hcard⟩ := h P
  exact ⟨F, hF, hcard⟩

end Witnesses

section Arith

theorem uc22p20v_two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem uc22p20v_two_pow_mod_three_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem uc22p20v_four_pow_mod_five (k : ℕ) : 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    generalize 4 ^ k = N at *
    omega

theorem uc22p20v_two_pow_mod_five_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 2 ^ (2 * k + 1) = 4 ^ k * 2 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [h]
  have := uc22p20v_four_pow_mod_five k
  generalize 4 ^ k = N at *
  omega

theorem uc22p20v_not_three_dvd_sub_one {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  have h := uc22p20v_two_pow_mod_three_odd hn
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  generalize 2 ^ n = N at *
  omega

theorem uc22p20v_not_five_dvd_sub_one {n : ℕ} (hn : Odd n) : ¬ 5 ∣ 2 ^ n - 1 := by
  have h := uc22p20v_two_pow_mod_five_odd hn
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  generalize 2 ^ n = N at *
  omega

theorem uc22p20v_not_three_dvd_add_one {n : ℕ} (hn : Even n) : ¬ 3 ∣ 2 ^ n + 1 := by
  have h := uc22p20v_two_pow_mod_three_even hn
  generalize 2 ^ n = N at *
  omega

theorem uc22p20v_ne_two_of_dvd_sub_one {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (h : p ∣ 2 ^ n - 1) :
    p ≠ 2 := by
  rintro rfl
  have hev : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)

theorem uc22p20v_ne_two_of_dvd_add_one {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (h : p ∣ 2 ^ n + 1) :
    p ≠ 2 := by
  rintro rfl
  have hev : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact (Nat.not_even_iff_odd.2 hev.add_one) (even_iff_two_dvd.2 h)

theorem uc22p20v_exists_prime_dvd_sub_one {n : ℕ} (hn : 2 ≤ n) : ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact ⟨(2 ^ n - 1).minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd _⟩

theorem uc22p20v_cast_eq_one {n p : ℕ} (h : p ∣ 2 ^ n - 1) : ((2 ^ n : ℕ) : ZMod p) = 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have := (ZMod.natCast_eq_zero_iff (2 ^ n - 1) p).2 h
  rw [Nat.cast_sub h1, Nat.cast_one] at this
  exact sub_eq_zero.1 this

theorem uc22p20v_cast_eq_neg_one {n p : ℕ} (h : p ∣ 2 ^ n + 1) : ((2 ^ n : ℕ) : ZMod p) = -1 := by
  have := (ZMod.natCast_eq_zero_iff (2 ^ n + 1) p).2 h
  rw [Nat.cast_add, Nat.cast_one] at this
  exact eq_neg_of_add_eq_zero_left this

end Arith

section Table

open CFSG.LocalAnalysis.RankThreeUC.S15

theorem uc22p20v_cast_three (n : ℕ) : ((2 ^ n : ℕ) : ZMod 3) = if Even n then 1 else -1 := by
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have : Even (2 * k) := even_two_mul k
    rw [if_pos this]
    push_cast
    rw [pow_mul, h2, one_pow]
  · have : ¬ Even (2 * k + 1) := by simp [Nat.even_add_one]
    rw [if_neg this]
    push_cast
    rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    decide

theorem uc22p20v_orderOf_neg_one_three : orderOf (-1 : ZMod 3) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem uc22p20v_eP_three (n : ℕ) : eP (2 ^ n) 3 = if Even n then 1 else 2 := by
  unfold eP
  rw [uc22p20v_cast_three]
  by_cases h : Even n
  · rw [if_pos h, if_pos h, orderOf_one]
  · rw [if_neg h, if_neg h]
    exact uc22p20v_orderOf_neg_one_three

theorem uc22p20v_eM_three (n : ℕ) : eM (2 ^ n) 3 = if Even n then 2 else 1 := by
  unfold eM
  rw [uc22p20v_cast_three]
  by_cases h : Even n
  · rw [if_pos h, if_pos h]
    exact uc22p20v_orderOf_neg_one_three
  · rw [if_neg h, if_neg h]
    have h1 : (-(-1 : ZMod 3)) = 1 := by decide
    exact (congrArg orderOf h1).trans orderOf_one

theorem uc22p20v_eS_three (n : ℕ) : eS (2 ^ n) 3 = 1 := by
  unfold eS
  rw [uc22p20v_cast_three]
  by_cases h : Even n
  · rw [if_pos h, one_pow, orderOf_one]
  · rw [if_neg h]
    have h1 : ((-1 : ZMod 3)) ^ 2 = 1 := by decide
    exact (congrArg orderOf h1).trans orderOf_one

theorem uc22p20v_eP_of_dvd {n p : ℕ} (h : p ∣ 2 ^ n - 1) : eP (2 ^ n) p = 1 := by
  unfold eP
  rw [uc22p20v_cast_eq_one h, orderOf_one]

theorem uc22p20v_eM_of_dvd {n p : ℕ} (h : p ∣ 2 ^ n + 1) : eM (2 ^ n) p = 1 := by
  unfold eM
  rw [uc22p20v_cast_eq_neg_one h, neg_neg, orderOf_one]

theorem uc22p20v_rkLin_true_one {m Q r z : ℕ} (h : eP Q r = 1) : m - 2 ≤ rkLin m true Q r z := by
  unfold rkLin
  simp only [h, if_true]
  split_ifs <;> omega

theorem uc22p20v_rkLin_true_one_of_not_dvd {m Q r z : ℕ} (h : eP Q r = 1) (hr : ¬ r ∣ m) :
    rkLin m true Q r z = m - 1 := by
  unfold rkLin
  simp [h, hr]

theorem uc22p20v_rkLin_false_one {m Q r z : ℕ} (h : eM Q r = 1) : m - 2 ≤ rkLin m false Q r z := by
  unfold rkLin
  simp only [h, Bool.false_eq_true, if_false, if_true]
  split_ifs <;> omega

theorem uc22p20v_rkLin_false_one_of_not_dvd {m Q r z : ℕ} (h : eM Q r = 1) (hr : ¬ r ∣ m) :
    rkLin m false Q r z = m - 1 := by
  unfold rkLin
  simp [h, hr]

theorem uc22p20v_rkLin_true_two {m Q r z : ℕ} (h : eP Q r = 2) : rkLin m true Q r z = m / 2 := by
  unfold rkLin
  simp [h]

theorem uc22p20v_rkLin_false_two {m Q r z : ℕ} (h : eM Q r = 2) : rkLin m false Q r z = m / 2 := by
  unfold rkLin
  simp [h]

theorem uc22p20v_rkSp_of_eS {l Q r : ℕ} (h : eS Q r = 1) : rkSp l Q r = l := by
  unfold rkSp
  rw [h, Nat.div_one]

theorem uc22p20v_rkOmMinus_ge {l Q r : ℕ} (h : eS Q r = 1) : l - 1 ≤ rkOmMinus l Q r := by
  unfold rkOmMinus
  rw [h, Nat.div_one]
  split_ifs <;> omega

theorem uc22p20v_rkOmPlus_ge {l Q r : ℕ} (hl : 4 ≤ l) (h : eS Q r = 1)
    (he : eP Q r = 1 ∨ eP Q r = 2) : 4 ≤ rkOmPlus l Q r := by
  unfold rkOmPlus
  rw [h, Nat.div_one]
  split_ifs with hc
  · rcases he with he | he
    · rw [he] at hc
      exact absurd (one_dvd l) hc.2
    · rw [he] at hc ⊢
      have : ¬ 2 ∣ l := hc.2
      omega
  · omega

theorem uc22p20v_rkG2_of_eS {Q r : ℕ} (h : eS Q r = 1) : rkG2 Q r = 2 := by
  unfold rkG2
  simp [h]

theorem uc22p20v_eP_three_cases (n : ℕ) : eP (2 ^ n) 3 = 1 ∨ eP (2 ^ n) 3 = 2 := by
  rw [uc22p20v_eP_three]
  split_ifs <;> simp

theorem uc22p20v_eM_three_cases (n : ℕ) : eM (2 ^ n) 3 = 1 ∨ eM (2 ^ n) 3 = 2 := by
  rw [uc22p20v_eM_three]
  split_ifs <;> simp

theorem uc22p20v_four_le_rkLin_true_one {m Q r z : ℕ} (hr : r.Prime) (h : eP Q r = 1) (hm : 5 ≤ m)
    (h5 : m = 5 → r ≠ 5) : 4 ≤ rkLin m true Q r z := by
  unfold rkLin
  simp only [h, if_true]
  by_cases hm5 : m = 5
  · subst hm5
    have : ¬ r ∣ 5 := fun hd => h5 rfl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 hd)
    simp [this]
  · split_ifs <;> omega

theorem uc22p20v_four_le_rkLin_false_one {m Q r z : ℕ} (hr : r.Prime) (h : eM Q r = 1) (hm : 5 ≤ m)
    (h5 : m = 5 → r ≠ 5) : 4 ≤ rkLin m false Q r z := by
  unfold rkLin
  simp only [h, Bool.false_eq_true, if_false, if_true]
  by_cases hm5 : m = 5
  · subst hm5
    have : ¬ r ∣ 5 := fun hd => h5 rfl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 hd)
    simp [this]
  · split_ifs <;> omega

theorem uc22p20v_four_le_rkLin_true_two {m Q r z : ℕ} (h : eP Q r = 2) (hm : 8 ≤ m) :
    4 ≤ rkLin m true Q r z := by
  have := uc22p20v_rkLin_true_two (m := m) (Q := Q) (r := r) (z := z) h
  omega

theorem uc22p20v_four_le_rkLin_false_two {m Q r z : ℕ} (h : eM Q r = 2) (hm : 8 ≤ m) :
    4 ≤ rkLin m false Q r z := by
  have := uc22p20v_rkLin_false_two (m := m) (Q := Q) (r := r) (z := z) h
  omega

theorem uc22p20v_rkLin_three_true {Q r z : ℕ} (h : eP Q r = 1) : rkLin 3 true Q r z = 2 := by
  unfold rkLin
  simp [h]

theorem uc22p20v_rkLin_three_false {Q r z : ℕ} (h : eM Q r = 1) : rkLin 3 false Q r z = 2 := by
  unfold rkLin
  simp [h]

theorem uc22p20v_two_le_rkLin_four_true {Q r z : ℕ} (h : eP Q r = 1 ∨ eP Q r = 2) :
    2 ≤ rkLin 4 true Q r z := by
  rcases h with h | h
  · have := uc22p20v_rkLin_true_one (m := 4) (Q := Q) (r := r) (z := z) h
    omega
  · have := uc22p20v_rkLin_true_two (m := 4) (Q := Q) (r := r) (z := z) h
    omega

theorem uc22p20v_two_le_rkLin_four_false {Q r z : ℕ} (h : eM Q r = 1 ∨ eM Q r = 2) :
    2 ≤ rkLin 4 false Q r z := by
  rcases h with h | h
  · have := uc22p20v_rkLin_false_one (m := 4) (Q := Q) (r := r) (z := z) h
    omega
  · have := uc22p20v_rkLin_false_two (m := 4) (Q := Q) (r := r) (z := z) h
    omega

theorem uc22p20v_rkLin_five_false {Q z : ℕ} (h : eM Q 5 = 1) (hz : 5 ∣ z) :
    rkLin 5 false Q 5 z = 4 := by
  unfold rkLin
  simp [h, hz]

end Table

section Centre

open CFSG.RankThree.PerfectCover
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

theorem uc22p20v_card_table_eq (t : StatedLieTag) (m n : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic t m 2 n × CFSG.Blueprint.Multiplier.exceptional t m 2 n) =
      (genericOrders t m 2 n).1 * (genericOrders t m 2 n).2 *
        ((exceptionalOrders t m 2 n).1 * (exceptionalOrders t m 2 n).2) := by
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

theorem uc22p20v_card_center_dvd (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {t : StatedLieTag} {m n : ℕ}
    (hM : LieModel (K ⧸ center K) t m 2 n) :
    Nat.card (center K) ∣ (genericOrders t m 2 n).1 * (genericOrders t m 2 n).2 := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  obtain ⟨-, ⟨eM⟩⟩ := hN (K ⧸ center K) t m 2 n hM
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.ksm_exc_two t m n
  have hM' : Nat.card (hopfMultiplier (K ⧸ center K)) =
      (genericOrders t m 2 n).1 * (genericOrders t m 2 n).2 * 2 ^ k := by
    rw [← hk, ← uc22p20v_card_table_eq,
      ← Nat.card_congr (hopfMultiplierEquivGriess (K ⧸ center K)).toEquiv]
    exact Nat.card_congr eM.toEquiv
  have hdvd := uc22p20r_card_center_dvd_hopf (MulEquiv.refl (K ⧸ center K))
  rw [hM'] at hdvd
  exact CFSG.LocalAnalysis.RankThreeUC.S15.ksm_odd_dvd hodd hdvd

theorem uc22p20v_center_eq_bot (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {t : StatedLieTag} {m n : ℕ}
    (hM : LieModel (K ⧸ center K) t m 2 n) (hg : genericOrders t m 2 n = (1, 1)) : center K = ⊥ := by
  have h := uc22p20v_card_center_dvd hN hq hodd hM
  rw [hg] at h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.1 (by simpa using h))

theorem uc22p20v_center_f4 (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ}
    (hM : LieModel (K ⧸ center K) .F4 m 2 n) : center K = ⊥ :=
  uc22p20v_center_eq_bot hN hq hodd hM rfl

theorem uc22p20v_center_e8 (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ}
    (hM : LieModel (K ⧸ center K) .E8 m 2 n) : center K = ⊥ :=
  uc22p20v_center_eq_bot hN hq hodd hM rfl

theorem uc22p20v_center_e7 (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {m n : ℕ} (hn : 1 ≤ n)
    (hM : LieModel (K ⧸ center K) .E7 m 2 n) : center K = ⊥ := by
  refine uc22p20v_center_eq_bot hN hq hodd hM ?_
  change (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
  rw [CFSG.LocalAnalysis.RankThreeUC.S15.ksm_gcd_two_odd
    (CFSG.LocalAnalysis.RankThreeUC.S15.ksm_odd_two_pow_sub_one hn)]

theorem uc22p20v_center_dvd_three_psl (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {n : ℕ}
    (hM : LieModel (K ⧸ center K) .PSL 3 2 n) : Nat.card (center K) ∣ 3 := by
  have h := uc22p20v_card_center_dvd hN hq hodd hM
  change Nat.card (center K) ∣ Nat.gcd 3 (2 ^ n - 1) * 1 at h
  rw [mul_one] at h
  exact h.trans (Nat.gcd_dvd_left _ _)

theorem uc22p20v_center_dvd_three_psu (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) {n : ℕ}
    (hM : LieModel (K ⧸ center K) .PSU 3 2 n) : Nat.card (center K) ∣ 3 := by
  have h := uc22p20v_card_center_dvd hN hq hodd hM
  change Nat.card (center K) ∣ Nat.gcd 3 (2 ^ n + 1) * 1 at h
  rw [mul_one] at h
  exact h.trans (Nat.gcd_dvd_left _ _)

theorem uc22p20v_center_dvd_five_psu (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K)))
    (hM : LieModel (K ⧸ center K) .PSU 5 2 2) : Nat.card (center K) ∣ 5 := by
  have h := uc22p20v_card_center_dvd hN hq hodd hM
  change Nat.card (center K) ∣ Nat.gcd 5 (2 ^ 2 + 1) * 1 at h
  rw [mul_one] at h
  exact h.trans (Nat.gcd_dvd_left _ _)

theorem uc22p20v_five_dvd_center_psu (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (center K))) (hZ : center K ≠ ⊥)
    (hM : LieModel (K ⧸ center K) .PSU 5 2 2) : 5 ∣ Nat.card (center K) := by
  rcases (Nat.dvd_prime Nat.prime_five).1 (uc22p20v_center_dvd_five_psu hN hq hodd hM) with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hZ
  · rw [h]

end Centre

section Models

theorem uc22p20v_exc_model {G : Type} [Group G] {t : StatedLieTag} {m p f : ℕ}
    (h : LieModel G t m p f) (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags) :
    m = 0 ∧ CFSG.Blueprint.ChevalleyExceptionalModel G t p f := by
  rcases h with ⟨h, -⟩ | ⟨hm, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact ⟨hm, h⟩
  · exact absurd h (by revert ht; cases t <;> decide)
  · exact absurd h (by revert ht; cases t <;> decide)

end Models

end CFSG.LocalAnalysis.UniquenessCase.UC22
