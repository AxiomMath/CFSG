module

public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

theorem A2_padicValNat_pow_mul {l f N0 P : ℕ} [hl : Fact l.Prime] (hP : ¬ l ∣ P) :
    padicValNat l ((l ^ f) ^ N0 * P) = f * N0 := by
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hP0 : P ≠ 0 := fun h => hP (h ▸ dvd_zero l)
  rw [padicValNat.mul (p := l) (pow_ne_zero _ (pow_ne_zero _ hl0)) hP0,
    padicValNat.eq_zero_of_not_dvd hP, add_zero, padicValNat.pow (p := l) (l ^ f) N0,
    padicValNat.prime_pow, mul_comm]

theorem A2_generic {l f n z P N0 D : ℕ} [hl : Fact l.Prime]
    (hn : n * z = (l ^ f) ^ N0 * P) (hP : ¬ l ∣ P) (hz : ¬ l ∣ z)
    (hPD : P < (l ^ f) ^ D) (hdim : D + N0 ≤ 3 * N0) :
    padicValNat l n = f * N0 ∧ n < l ^ (3 * padicValNat l n) := by
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hQ0 : l ^ f ≠ 0 := pow_ne_zero _ hl0
  have hP0 : P ≠ 0 := fun h => hP (h ▸ dvd_zero l)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ dvd_zero l)
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hn
    exact mul_ne_zero (pow_ne_zero _ hQ0) hP0 hn.symm
  have hv : padicValNat l n = f * N0 := by
    have h1 := padicValNat.mul (p := l) hn0 hz0
    rw [hn, A2_padicValNat_pow_mul hP, padicValNat.eq_zero_of_not_dvd hz, add_zero] at h1
    exact h1.symm
  refine ⟨hv, ?_⟩
  have hpos : 0 < (l ^ f) ^ N0 := Nat.pos_of_ne_zero (pow_ne_zero _ hQ0)
  have hlt : n * z < (l ^ f) ^ (3 * N0) := by
    calc n * z = (l ^ f) ^ N0 * P := hn
      _ < (l ^ f) ^ N0 * (l ^ f) ^ D := mul_lt_mul_of_pos_left hPD hpos
      _ = (l ^ f) ^ (N0 + D) := by rw [pow_add]
      _ ≤ (l ^ f) ^ (3 * N0) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hQ0) (by omega)
  have hle : n ≤ n * z := Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hz0)
  have hpow : l ^ (3 * padicValNat l n) = (l ^ f) ^ (3 * N0) := by
    rw [hv, show 3 * (f * N0) = f * (3 * N0) by ring, pow_mul]
  rw [hpow]
  exact lt_of_le_of_lt hle hlt

theorem A2_prod_sub_lt {Q a : ℕ} {c : ℕ → ℕ} (hQ : 0 < Q) {n : ℕ} (han : a ≤ n) :
    ∏ j ∈ Finset.Icc a n, (Q ^ c j - 1) < Q ^ (∑ j ∈ Finset.Icc a n, c j) := by
  induction n, han using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.prod_singleton, Finset.sum_singleton]
    exact Nat.sub_lt (pow_pos hQ _) one_pos
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (show a ≤ n + 1 by omega),
      Finset.sum_Icc_succ_top (show a ≤ n + 1 by omega), pow_add]
    have hlt : Q ^ c (n + 1) - 1 < Q ^ c (n + 1) := Nat.sub_lt (pow_pos hQ _) one_pos
    exact mul_lt_mul'' ih hlt (Nat.zero_le _) (Nat.zero_le _)

theorem A2_not_dvd_pow_sub_one {l Q k : ℕ} [hl : Fact l.Prime] (hQ : 0 < Q) (hlQ : l ∣ Q)
    (hk : k ≠ 0) : ¬ l ∣ Q ^ k - 1 := by
  intro h
  have hpos : 1 ≤ Q ^ k := Nat.one_le_pow _ _ hQ
  have h2 : l ∣ Q ^ k - 1 + 1 := by
    rw [Nat.sub_add_cancel hpos]
    exact dvd_pow hlQ hk
  exact hl.out.not_dvd_one ((Nat.dvd_add_right h).mp h2)

theorem A2_not_dvd_gcd_sub_one {l Q n : ℕ} [hl : Fact l.Prime] (hQ : 0 < Q) (hlQ : l ∣ Q) :
    ¬ l ∣ Nat.gcd (Q - 1) n := by
  intro h
  have h1 : l ∣ Q - 1 := h.trans (Nat.gcd_dvd_left _ _)
  have h2 : l ∣ Q - 1 + 1 := by
    rw [Nat.sub_add_cancel hQ]
    exact hlQ
  exact hl.out.not_dvd_one ((Nat.dvd_add_right h1).mp h2)

theorem A2_not_dvd_prod {l Q a : ℕ} {c : ℕ → ℕ} [hl : Fact l.Prime] (hQ : 0 < Q)
    (hlQ : l ∣ Q) (hc : ∀ j, a ≤ j → c j ≠ 0) {n : ℕ} :
    ¬ l ∣ ∏ j ∈ Finset.Icc a n, (Q ^ c j - 1) := by
  intro h
  obtain ⟨j, hj, hdvd⟩ :=
    ((Nat.Prime.prime hl.out).dvd_finsetProd_iff (fun j => Q ^ c j - 1)).mp h
  exact A2_not_dvd_pow_sub_one hQ hlQ (hc j (Finset.mem_Icc.mp hj).1) hdvd

theorem A2_two_sum_Icc (m : ℕ) :
    2 * (∑ j ∈ Finset.Icc 2 (m + 2), j) + 2 = (m + 2) * (m + 3) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by ring,
      Finset.sum_Icc_succ_top (show 2 ≤ (m + 2) + 1 by omega)]
    nlinarith [ih]

theorem A2_two_mul_half (m : ℕ) : 2 * ((m + 2) * (m + 1) / 2) = (m + 2) * (m + 1) :=
  Nat.two_mul_div_two_of_even (by rw [mul_comm]; exact Nat.even_mul_succ_self (m + 1))

theorem A2_sum_le (m : ℕ) :
    (∑ j ∈ Finset.Icc 2 (m + 2), j) + (m + 2) * (m + 1) / 2 ≤
      3 * ((m + 2) * (m + 1) / 2) := by
  have h1 := A2_two_sum_Icc m
  have h2 := A2_two_mul_half m
  nlinarith [Nat.zero_le (m * m), Nat.zero_le m]

theorem A2_not_dvd_sub_one {l Q : ℕ} [hl : Fact l.Prime] (hQ : 0 < Q) (hlQ : l ∣ Q) :
    ¬ l ∣ Q - 1 := by
  intro h
  have h2 : l ∣ Q - 1 + 1 := by
    rw [Nat.sub_add_cancel hQ]
    exact hlQ
  exact hl.out.not_dvd_one ((Nat.dvd_add_right h).mp h2)

theorem A2_not_dvd_pow_add_one {l Q k : ℕ} [hl : Fact l.Prime] (hlQ : l ∣ Q) (hk : k ≠ 0) :
    ¬ l ∣ Q ^ k + 1 :=
  fun h => hl.out.not_dvd_one ((Nat.dvd_add_right (dvd_pow hlQ hk)).mp h)

theorem A2_not_dvd_add_one {l Q : ℕ} [hl : Fact l.Prime] (hlQ : l ∣ Q) :
    ¬ l ∣ Q + 1 := by
  simpa using A2_not_dvd_pow_add_one (k := 1) hlQ one_ne_zero

theorem A2_f_ne_zero {l f : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = l ^ f) :
    f ≠ 0 := by
  rintro rfl
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK, pow_zero] at h1
  exact lt_irrefl 1 h1

theorem A2_dvd_pow {l f : ℕ} (hf : f ≠ 0) : l ∣ l ^ f := dvd_pow_self l hf

theorem A2_prod_id_lt {Q a n : ℕ} (hQ : 0 < Q) (han : a ≤ n) :
    ∏ j ∈ Finset.Icc a n, (Q ^ j - 1) < Q ^ (∑ j ∈ Finset.Icc a n, j) :=
  A2_prod_sub_lt (c := fun j => j) hQ han

theorem A2_sum_two_mul_Icc (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, 2 * j = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega), ih]
    ring

theorem A2_su3_lt {Q : ℕ} (hQ : 1 ≤ Q) : (Q ^ 2 - 1) * (Q ^ 3 + 1) < Q ^ 5 := by
  obtain ⟨A, hA⟩ : ∃ A, A + 1 = Q ^ 2 :=
    ⟨Q ^ 2 - 1, Nat.sub_add_cancel (Nat.one_le_pow _ _ hQ)⟩
  have hAQ : Q ^ 2 - 1 = A := by omega
  have h5 : Q ^ 5 = Q ^ 3 * (A + 1) := by rw [hA]; ring
  have hA3 : A < Q ^ 3 := by
    have : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right hQ (by norm_num)
    omega
  rw [hAQ, h5]
  nlinarith [hA3]

theorem A2_suz_lt {Q : ℕ} (hQ : 1 ≤ Q) : (Q - 1) * (Q ^ 2 + 1) < Q ^ 3 := by
  obtain ⟨B, rfl⟩ : ∃ B, Q = B + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h : B * ((B + 1) ^ 2 + 1) + (B ^ 2 + B + 1) = (B + 1) ^ 3 := by ring
  omega

theorem A2_g2_lt {Q : ℕ} (hQ : 0 < Q) : (Q ^ 6 - 1) * (Q ^ 2 - 1) < Q ^ 8 := by
  have h1 : Q ^ 6 - 1 < Q ^ 6 := Nat.sub_lt (pow_pos hQ _) one_pos
  have h2 : Q ^ 2 - 1 < Q ^ 2 := Nat.sub_lt (pow_pos hQ _) one_pos
  have h3 : Q ^ 8 = Q ^ 6 * Q ^ 2 := by ring
  rw [h3]
  exact mul_lt_mul'' h1 h2 (Nat.zero_le _) (Nat.zero_le _)

theorem A2_psl2 {l f : ℕ} {K : Type} [Field K] [Finite K] [hl : Fact l.Prime]
    (hK : Nat.card K = l ^ f) :
    padicValNat l (Nat.card (CFSG.GorensteinWalter.PSL2 K)) = f ∧
      Nat.card (CFSG.GorensteinWalter.PSL2 K) <
        l ^ (3 * padicValNat l (Nat.card (CFSG.GorensteinWalter.PSL2 K))) := by
  have hf := A2_f_ne_zero hK
  have hlQ : l ∣ l ^ f := A2_dvd_pow hf
  have hQ : 0 < l ^ f := pow_pos hl.out.pos f
  have h := CFSG.RankThree.PartTwo.KFacts.card_psl_mul_gcd (K := K) (n := 2) (by norm_num)
  rw [hK, show Finset.Icc 2 2 = {2} from rfl, Finset.prod_singleton] at h
  have hn : Nat.card (CFSG.GorensteinWalter.PSL2 K) * Nat.gcd (l ^ f - 1) 2 =
      (l ^ f) ^ 1 * ((l ^ f) ^ 2 - 1) := by
    rw [h]
  obtain ⟨h1, h2⟩ := A2_generic hn (A2_not_dvd_pow_sub_one hQ hlQ two_ne_zero)
    (A2_not_dvd_gcd_sub_one hQ hlQ) (Nat.sub_lt (pow_pos hQ _) one_pos) (by norm_num)
  exact ⟨h1.trans (mul_one f), h2⟩

theorem A2_projSL {l f n : ℕ} {K : Type} [Field K] [Finite K] [hl : Fact l.Prime]
    (hK : Nat.card K = l ^ f) (hn : 2 ≤ n) :
    padicValNat l (Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) =
        f * (n * (n - 1) / 2) ∧
      Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) <
        l ^ (3 * padicValNat l
          (Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  have hQ : 0 < l ^ f := pow_pos hl.out.pos f
  have hlQ : l ∣ l ^ f := A2_dvd_pow (A2_f_ne_zero hK)
  have h := CFSG.RankThree.PartTwo.KFacts.card_projectiveSL_mul_card_scalars
    (K := K) (n := m + 2) (by omega)
  rw [hK, show m + 2 - 1 = m + 1 by omega] at h
  have hZ : Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m + 2) K) ∣
      l ^ f - 1 := by
    have := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_scalars_dvd
      (K := K) (n := m + 2) (by omega)
    rw [hK] at this
    exact this
  have hz : ¬ l ∣ Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars (m + 2) K) :=
    fun h' => A2_not_dvd_sub_one hQ hlQ (h'.trans hZ)
  obtain ⟨h1, h2⟩ := A2_generic h
    (A2_not_dvd_prod (a := 2) (c := fun j => j) hQ hlQ (fun j hj => show j ≠ 0 by omega))
    hz (A2_prod_id_lt hQ (by omega)) (A2_sum_le m)
  exact ⟨h1, h2⟩

theorem A2_sl {l f n : ℕ} {K : Type} [Field K] [Finite K] [hl : Fact l.Prime]
    (hK : Nat.card K = l ^ f) (hn : 2 ≤ n) :
    padicValNat l (Nat.card (Matrix.SpecialLinearGroup (Fin n) K)) = f * (n * (n - 1) / 2) ∧
      Nat.card (Matrix.SpecialLinearGroup (Fin n) K) <
        l ^ (3 * padicValNat l (Nat.card (Matrix.SpecialLinearGroup (Fin n) K))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  have hQ : 0 < l ^ f := pow_pos hl.out.pos f
  have hlQ : l ∣ l ^ f := A2_dvd_pow (A2_f_ne_zero hK)
  have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
    (K := K) (n := m + 2) (by omega)
  rw [hK, show m + 2 - 1 = m + 1 by omega] at h
  have hn' : Nat.card (Matrix.SpecialLinearGroup (Fin (m + 2)) K) * 1 =
      (l ^ f) ^ ((m + 2) * (m + 1) / 2) * ∏ j ∈ Finset.Icc 2 (m + 2), ((l ^ f) ^ j - 1) := by
    rw [mul_one]
    exact h
  obtain ⟨h1, h2⟩ := A2_generic hn'
    (A2_not_dvd_prod (a := 2) (c := fun j => j) hQ hlQ (fun j hj => show j ≠ 0 by omega))
    (Nat.Prime.not_dvd_one hl.out) (A2_prod_id_lt hQ (by omega)) (A2_sum_le m)
  exact ⟨h1, h2⟩

theorem A2_psu3 {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) :
    padicValNat p (Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3)) = f * 3 ∧
      Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3) <
        p ^ (3 * padicValNat p (Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3))) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hf : f ≠ 0 := by have := h.one_le; omega
  have hlQ : p ∣ p ^ f := A2_dvd_pow hf
  have hQ : 0 < p ^ f := pow_pos h.prime.pos f
  have hn : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    rw [CFSG.RankThree.PartTwo.KFacts.card_unitaryPSU_three_mul_gcd h, mul_assoc]
  have hP : ¬ p ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := fun hd =>
    (h.prime.dvd_mul.mp hd).elim
      (fun h1 => A2_not_dvd_pow_sub_one hQ hlQ two_ne_zero h1)
      (fun h1 => A2_not_dvd_pow_add_one (k := 3) hlQ (by norm_num) h1)
  have hz : ¬ p ∣ Nat.gcd 3 (p ^ f + 1) := fun hd =>
    A2_not_dvd_add_one hlQ (hd.trans (Nat.gcd_dvd_right _ _))
  obtain ⟨h1, h2⟩ := A2_generic hn hP hz (A2_su3_lt hQ) (by norm_num)
  exact ⟨h1, h2⟩

theorem A2_su3 {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) :
    padicValNat p (Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3)) = f * 3 ∧
      Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) <
        p ^ (3 * padicValNat p (Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3))) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hf : f ≠ 0 := by have := h.one_le; omega
  have hlQ : p ∣ p ^ f := A2_dvd_pow hf
  have hQ : 0 < p ^ f := pow_pos h.prime.pos f
  have hn : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) * 1 =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
    rw [mul_one, CFSG.RankThree.PartTwo.KFacts.card_unitarySU_three h, mul_assoc]
  have hP : ¬ p ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := fun hd =>
    (h.prime.dvd_mul.mp hd).elim
      (fun h1 => A2_not_dvd_pow_sub_one hQ hlQ two_ne_zero h1)
      (fun h1 => A2_not_dvd_pow_add_one (k := 3) hlQ (by norm_num) h1)
  obtain ⟨h1, h2⟩ := A2_generic hn hP (Nat.Prime.not_dvd_one h.prime) (A2_su3_lt hQ)
    (by norm_num)
  exact ⟨h1, h2⟩

theorem A2_prod_two_mul_lt {Q n : ℕ} (hQ : 0 < Q) (hn : 1 ≤ n) :
    ∏ j ∈ Finset.Icc 1 n, (Q ^ (2 * j) - 1) < Q ^ (n * (n + 1)) := by
  have h : ∏ j ∈ Finset.Icc 1 n, (Q ^ (2 * j) - 1) < Q ^ (∑ j ∈ Finset.Icc 1 n, 2 * j) :=
    A2_prod_sub_lt (c := fun j => 2 * j) hQ hn
  rw [A2_sum_two_mul_Icc] at h
  exact h

theorem A2_psp {p f : ℕ} {K : Type} [Field K] [Finite K] [hp : Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ f) {n : ℕ} (hn : 1 ≤ n) :
    padicValNat p (Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))) = f * n ^ 2 ∧
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) <
        p ^ (3 * padicValNat p (Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)))) := by
  have hf := A2_f_ne_zero hK
  have hlQ : p ∣ p ^ f := A2_dvd_pow hf
  have hQ : 0 < p ^ f := pow_pos hp.out.pos f
  have hPD : ∏ j ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * j) - 1) < (p ^ f) ^ (n * (n + 1)) :=
    A2_prod_two_mul_lt hQ hn
  have hP : ¬ p ∣ ∏ j ∈ Finset.Icc 1 n, ((p ^ f) ^ (2 * j) - 1) :=
    A2_not_dvd_prod (a := 1) (c := fun j => 2 * j) hQ hlQ (fun j hj => show 2 * j ≠ 0 by omega)
  have hdim : n * (n + 1) + n ^ 2 ≤ 3 * n ^ 2 := by nlinarith [hn, Nat.zero_le n]
  rcases eq_or_ne p 2 with rfl | hp2
  ·
    have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := K) n
    rw [hK] at h
    have hn' : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) * 1 =
        (2 ^ f) ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, ((2 ^ f) ^ (2 * j) - 1) := by
      rw [mul_one]
      exact h
    obtain ⟨h1, h2⟩ := A2_generic hn' hP (Nat.Prime.not_dvd_one hp.out) hPD hdim
    exact ⟨h1, h2⟩
  ·
    have h2K : (2 : K) ≠ 0 := by
      intro h0
      have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp
        ((CharP.cast_eq_zero_iff K p 2).mp h'))
    have h := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero h2K hn
    rw [hK] at h
    have hz : ¬ p ∣ 2 := fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd)
    obtain ⟨h1, h2⟩ := A2_generic h hP hz hPD hdim
    exact ⟨h1, h2⟩

theorem A2_sz {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    padicValNat 2 (Nat.card (CFSG.Blueprint.suzukiGroup a K)) = (2 * a + 1) * 2 ∧
      Nat.card (CFSG.Blueprint.suzukiGroup a K) <
        2 ^ (3 * padicValNat 2 (Nat.card (CFSG.Blueprint.suzukiGroup a K))) := by
  have hQ : 0 < 2 ^ (2 * a + 1) := pow_pos (by norm_num) _
  have hlQ : 2 ∣ 2 ^ (2 * a + 1) := A2_dvd_pow (by omega)
  have h := CFSG.LieType.Ree.suzuki_order (a := a) (K := K) hK
  have hn : Nat.card (CFSG.Blueprint.suzukiGroup a K) * 1 =
      (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
    rw [mul_one, h, mul_assoc]
  have hP : ¬ 2 ∣ (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := fun hd =>
    (Nat.prime_two.dvd_mul.mp hd).elim
      (fun h1 => A2_not_dvd_sub_one hQ hlQ h1)
      (fun h1 => A2_not_dvd_pow_add_one (k := 2) hlQ (by norm_num) h1)
  obtain ⟨h1, h2⟩ := A2_generic hn hP (Nat.Prime.not_dvd_one Nat.prime_two)
    (A2_suz_lt Nat.one_le_two_pow) (by norm_num)
  exact ⟨h1, h2⟩

open CFSG.Blueprint.Chevalley in
theorem A2_g2 {l f : ℕ} {K : Type} [Field K] [Finite K] [Fact l.Prime]
    (hK : Nat.card K = l ^ f) :
    padicValNat l (Nat.card (adjointGroup .G2 K)) = f * 6 ∧
      Nat.card (adjointGroup .G2 K) < l ^ (3 * padicValNat l (Nat.card (adjointGroup .G2 K))) := by
  have hlQ : l ∣ l ^ f := A2_dvd_pow (A2_f_ne_zero hK)
  have hQ : 0 < l ^ f := pow_pos (Nat.Prime.pos (Fact.out (p := l.Prime))) f
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)
  rw [CFSG.Open.ordG2, hK] at h
  have hn : Nat.card (adjointGroup .G2 K) * 1 =
      (l ^ f) ^ 6 * (((l ^ f) ^ 6 - 1) * ((l ^ f) ^ 2 - 1)) := by
    rw [mul_one, h, mul_assoc]
  have hlp : l.Prime := Fact.out
  have hP : ¬ l ∣ ((l ^ f) ^ 6 - 1) * ((l ^ f) ^ 2 - 1) := fun hd =>
    (hlp.dvd_mul.mp hd).elim
      (fun h1 => A2_not_dvd_pow_sub_one hQ hlQ (by norm_num) h1)
      (fun h1 => A2_not_dvd_pow_sub_one hQ hlQ (by norm_num) h1)
  obtain ⟨h1, h2⟩ := A2_generic hn hP hlp.not_dvd_one (A2_g2_lt hQ) (by norm_num)
  exact ⟨h1, h2⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

end
