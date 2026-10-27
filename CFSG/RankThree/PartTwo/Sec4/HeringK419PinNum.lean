module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofArith

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.RankThree.PartTwo.KFacts.OddChar

inductive XOrd (M p e : ℕ) : Prop
  | sl (n g : ℕ) (hn : 4 ≤ n) (hg : g ∣ p ^ e - 1)
      (h : M * g = (p ^ e) ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, ((p ^ e) ^ j - 1))
  | spOdd (r : ℕ) (hr : 2 ≤ r) (hp : p ≠ 2)
      (h : M * 2 = (p ^ e) ^ (r ^ 2) * ∏ j ∈ Icc 1 r, ((p ^ e) ^ (2 * j) - 1))
  | spEven (r : ℕ) (hr : 3 ≤ r) (hp : p = 2)
      (h : M = (p ^ e) ^ (r ^ 2) * ∏ j ∈ Icc 1 r, ((p ^ e) ^ (2 * j) - 1))

structure XInfo (M p e : ℕ) : Prop where
  prime : p.Prime
  ex : ∃ k, 8 ≤ k ∧ p ^ k ∣ M ∧ ¬ p ^ (k + 1) ∣ M ∧ M ^ 2 < (p ^ k) ^ 5
  two : p ≠ 2 → 2 ^ (8 * padicValNat 2 M) ≤ M ^ 3
  prof : p = 2 → ∃ (Z : ℕ → Prop) (N w : ℕ), Profile M N Z ∧ (∀ k, Z k → k ≤ w) ∧ 6 ≤ w ∧
    w < N

theorem slOrd_lt {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : 2 ≤ n) :
    q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1) < q ^ (n ^ 2 - 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (by positivity) one_pos
    have hq0 : 0 < q := by omega
    calc q ^ (2 * (2 - 1) / 2) * ∏ j ∈ Icc 2 2, (q ^ j - 1) = q * (q ^ 2 - 1) := by
          rw [show 2 * (2 - 1) / 2 = 1 from rfl, show Icc 2 2 = {2} by rfl, prod_singleton,
            pow_one]
      _ < q * q ^ 2 := Nat.mul_lt_mul_of_pos_left h2 hq0
      _ = q ^ (2 ^ 2 - 1) := by rw [show (2 : ℕ) ^ 2 - 1 = 3 by norm_num]; ring
  | succ n hn ih =>
    rw [slOrd_succ q (by omega)]
    have h1 : q ^ n * (q ^ (n + 1) - 1) < q ^ n * q ^ (n + 1) :=
      Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (by positivity) one_pos) (by positivity)
    have e : n ^ 2 - 1 + (n + (n + 1)) = (n + 1) ^ 2 - 1 := by
      have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this, show 1 ≤ (n + 1) ^ 2 from Nat.one_le_pow _ _ (by omega)]
      ring
    calc q ^ (n * (n - 1) / 2) * (∏ j ∈ Icc 2 n, (q ^ j - 1)) * (q ^ n * (q ^ (n + 1) - 1))
        < q ^ (n ^ 2 - 1) * (q ^ n * q ^ (n + 1)) := Nat.mul_lt_mul'' ih h1
      _ = q ^ ((n + 1) ^ 2 - 1) := by rw [← pow_add, ← pow_add, e]

theorem spOrd_lt {q : ℕ} (hq : 2 ≤ q) {r : ℕ} (hr : 1 ≤ r) :
    q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1) < q ^ (2 * r ^ 2 + r) := by
  induction r, hr using Nat.le_induction with
  | base =>
    have h2 : q ^ 2 - 1 < q ^ 2 := Nat.sub_lt (by positivity) one_pos
    have hq0 : 0 < q := by omega
    calc q ^ (1 ^ 2) * ∏ j ∈ Icc 1 1, (q ^ (2 * j) - 1) = q * (q ^ 2 - 1) := by
          rw [show Icc 1 1 = {1} by rfl, prod_singleton, one_pow, pow_one, mul_one]
      _ < q * q ^ 2 := Nat.mul_lt_mul_of_pos_left h2 hq0
      _ = q ^ (2 * 1 ^ 2 + 1) := by rw [show 2 * 1 ^ 2 + 1 = 3 by norm_num]; ring
  | succ r hr ih =>
    rw [spOrd_succ]
    have h1 : q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1) <
        q ^ (2 * (r + 1) - 1) * q ^ (2 * (r + 1)) :=
      Nat.mul_lt_mul_of_pos_left (Nat.sub_lt (by positivity) one_pos) (by positivity)
    have e : 2 * r ^ 2 + r + (2 * (r + 1) - 1 + 2 * (r + 1)) = 2 * (r + 1) ^ 2 + (r + 1) := by
      rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega]
      ring
    calc q ^ (r ^ 2) * (∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1)) *
          (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1))
        < q ^ (2 * r ^ 2 + r) * (q ^ (2 * (r + 1) - 1) * q ^ (2 * (r + 1))) :=
          Nat.mul_lt_mul'' ih h1
      _ = q ^ (2 * (r + 1) ^ 2 + (r + 1)) := by rw [← pow_add, ← pow_add, e]

theorem not_dvd_pow_pow_sub_one {p e j : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hj : 1 ≤ j) :
    ¬ p ∣ (p ^ e) ^ j - 1 :=
  CFSG.RankThree.PartTwo.Sec11.KSListsProof.not_dvd_pow_sub_one hp (dvd_pow_self p (by omega))
    (Nat.one_le_pow _ _ hp.pos) hj

theorem not_dvd_prod_pow_sub_one {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (J : Finset ℕ)
    (c : ℕ → ℕ) (hc : ∀ j ∈ J, 1 ≤ c j) : ¬ p ∣ ∏ j ∈ J, ((p ^ e) ^ c j - 1) := by
  intro h
  obtain ⟨j, hj, h⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp h
  exact not_dvd_pow_pow_sub_one hp he (hc j hj) h

theorem exact_pow_of_mul_eq {p k M g Q : ℕ} (hp : p.Prime) (hg : ¬ p ∣ g) (hQ : ¬ p ∣ Q)
    (h : M * g = p ^ k * Q) : p ^ k ∣ M ∧ ¬ p ^ (k + 1) ∣ M := by
  refine ⟨?_, fun hM => ?_⟩
  · have hc : Nat.Coprime (p ^ k) g :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hg)
    exact hc.dvd_of_dvd_mul_right (h ▸ Dvd.intro _ rfl)
  · have h1 : p ^ (k + 1) ∣ p ^ k * Q := h ▸ Dvd.dvd.mul_right hM g
    rw [pow_succ] at h1
    exact hQ (by simpa using (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos k) h1))

theorem nine_le_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 2 ≤ e) : 9 ≤ p ^ e := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he

theorem tri_facts {n T : ℕ} (hn : 4 ≤ n) (hT2 : 2 * T = n * (n - 1)) :
    6 ≤ T ∧ n < T ∧ 2 * (n ^ 2 - 1) ≤ 5 * T := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hT2
  have e : (m + 1) ^ 2 - 1 = m ^ 2 + 2 * m := by
    have : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [this]; ring
  rw [e]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem xinfo_sl {M p e n g : ℕ} (hp : p.Prime) (he : 2 ≤ e) (hn : 4 ≤ n) (hg : g ∣ p ^ e - 1)
    (h : M * g = (p ^ e) ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, ((p ^ e) ^ j - 1)) :
    XInfo M p e := by
  set q := p ^ e with hq
  set T := n * (n - 1) / 2 with hT
  have hT2 : 2 * T = n * (n - 1) := by
    rw [hT]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  obtain ⟨hT6, hnT, h5⟩ := tri_facts hn hT2
  have hq2 : 2 ≤ q := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hqk : q ^ T = p ^ (e * T) := by rw [hq, ← pow_mul]
  have hP : ¬ p ∣ ∏ j ∈ Icc 2 n, (q ^ j - 1) :=
    not_dvd_prod_pow_sub_one hp (by omega) _ (fun j => j)
      (fun j hj => by have := (mem_Icc.mp hj).1; show 1 ≤ j; omega)
  have hpg : ¬ p ∣ g := by
    intro hpg
    have h1 : p ∣ p ^ e - 1 := hpg.trans hg
    have h2 := not_dvd_pow_pow_sub_one (p := p) (e := e) (j := 1) hp (by omega) le_rfl
    rw [pow_one] at h2
    exact h2 h1
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hg (by
    have : 2 ≤ q := hq2
    omega)
  rw [hqk] at h
  have hdiv := exact_pow_of_mul_eq hp hpg hP h
  have hSl := slOrd_lt hq2 (show 2 ≤ n by omega)
  have hMlt : M < q ^ (n ^ 2 - 1) :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right M hg0) (by rw [h, ← hqk]; exact hSl)
  refine ⟨hp, ⟨e * T, by nlinarith, hdiv.1, hdiv.2, ?_⟩, fun hp2 => ?_, fun hp2 => ?_⟩
  · calc M ^ 2 < (q ^ (n ^ 2 - 1)) ^ 2 := Nat.pow_lt_pow_left hMlt (by norm_num)
      _ = q ^ (2 * (n ^ 2 - 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ q ^ (5 * T) := Nat.pow_le_pow_right (by omega) h5
      _ = (p ^ (e * T)) ^ 5 := by rw [mul_comm 5 T, pow_mul, hqk]
  · have hpodd : Odd q := (hp.odd_of_ne_two hp2).pow
    have h3 : 3 ≤ q := by have := nine_le_pow hp hp2 he; omega
    have hh : M * g = q ^ (n * (n - 1) / 2) * ∏ j ∈ Icc 2 n, (q ^ j - 1) := by
      rw [h, hqk]
    exact two_pow_le_of_mul_eq_slOrd hpodd h3 (by omega) hh hg
  · subst hp2
    have hP' : Odd (∏ j ∈ Icc 2 n, ((2 ^ e) ^ j - 1)) :=
      odd_prod fun j hj => odd_pow_sub_one (by omega) (by simp at hj; omega)
    refine ⟨fun k => ∃ i ∈ Icc 2 n, k ∣ e * i, e * T, e * n, ?_, ?_, by nlinarith, ?_⟩
    · refine Profile.of_div ?_ hP' hg ?_ hg0 fun p' k hp' hk => ?_
      · have : M = M * g / g := (Nat.mul_div_cancel M hg0).symm
        rw [this, h]
      · have h23 : ({2, 3} : Finset ℕ) ⊆ Icc 2 n := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          simp only [mem_Icc]; omega
        have := Finset.prod_dvd_prod_of_subset _ _ (fun j => (2 ^ e) ^ j - 1) h23
        rw [Finset.prod_pair (by norm_num)] at this
        exact (mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one _ 2)
          (Nat.sub_one_dvd_pow_sub_one _ 3)).trans this
      · rw [(Nat.Prime.prime hp'.prime).dvd_finsetProd_iff]
        exact exists_congr fun i => and_congr_right fun _ =>
          PrimDiv.dvd_pow_sub_one_iff hp' hk e i
    · rintro k ⟨i, hi, hk⟩
      simp only [mem_Icc] at hi
      exact (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hk).trans
        (Nat.mul_le_mul_left _ hi.2)
    · exact Nat.mul_lt_mul_of_pos_left hnT (by omega)

theorem xinfo_spOdd {M p e r : ℕ} (hp : p.Prime) (he : 2 ≤ e) (hr : 2 ≤ r) (hp2 : p ≠ 2)
    (h : M * 2 = (p ^ e) ^ (r ^ 2) * ∏ j ∈ Icc 1 r, ((p ^ e) ^ (2 * j) - 1)) :
    XInfo M p e := by
  set q := p ^ e with hq
  have hq9 : 9 ≤ q := nine_le_pow hp hp2 he
  have hq2 : 2 ≤ q := by omega
  have hqk : q ^ (r ^ 2) = p ^ (e * r ^ 2) := by rw [hq, ← pow_mul]
  have hP : ¬ p ∣ ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1) :=
    not_dvd_prod_pow_sub_one hp (by omega) _ (fun j => 2 * j)
      (fun j hj => by have := (mem_Icc.mp hj).1; show 1 ≤ 2 * j; omega)
  have hp2' : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  rw [hqk] at h
  have hdiv := exact_pow_of_mul_eq hp hp2' hP h
  have hSp := spOrd_lt hq2 (show 1 ≤ r by omega)
  have hMlt : M < q ^ (2 * r ^ 2 + r) :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right M (show 0 < 2 by norm_num))
      (by rw [h, ← hqk]; exact hSp)
  have hr4 : 4 ≤ r ^ 2 := by nlinarith
  refine ⟨hp, ⟨e * r ^ 2, by nlinarith, hdiv.1, hdiv.2, ?_⟩, fun _ => ?_,
    fun hp2' => absurd hp2' hp2⟩
  · calc M ^ 2 < (q ^ (2 * r ^ 2 + r)) ^ 2 := Nat.pow_lt_pow_left hMlt (by norm_num)
      _ = q ^ (2 * (2 * r ^ 2 + r)) := by rw [← pow_mul, mul_comm]
      _ ≤ q ^ (5 * r ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = (p ^ (e * r ^ 2)) ^ 5 := by rw [mul_comm 5 (r ^ 2), pow_mul, hqk]
  · have hodd : Odd q := (hp.odd_of_ne_two hp2).pow
    have hh : M * 2 = q ^ (r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1) := by rw [h, hqk]
    refine two_pow_le_of_mul_two_eq_spOrd hodd (by omega) ?_ hh
    by_cases hr3 : 3 ≤ r
    · exact Or.inl hr3
    · exact Or.inr ⟨by omega, by omega⟩

theorem xinfo_spEven {M e r : ℕ} (he : 2 ≤ e) (hr : 3 ≤ r)
    (h : M = (2 ^ e) ^ (r ^ 2) * ∏ j ∈ Icc 1 r, ((2 ^ e) ^ (2 * j) - 1)) :
    XInfo M 2 e := by
  have hp := Nat.prime_two
  set q := 2 ^ e with hq
  have hq2 : 2 ≤ q := le_trans hp.two_le (Nat.le_self_pow (by omega) 2)
  have hqk : q ^ (r ^ 2) = 2 ^ (e * r ^ 2) := by rw [hq, ← pow_mul]
  have hP : ¬ 2 ∣ ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1) :=
    not_dvd_prod_pow_sub_one hp (by omega) _ (fun j => 2 * j)
      (fun j hj => by have := (mem_Icc.mp hj).1; show 1 ≤ 2 * j; omega)
  have hSp := spOrd_lt hq2 (show 1 ≤ r by omega)
  have hMlt : M < q ^ (2 * r ^ 2 + r) := by rw [h]; exact hSp
  have h1 : M * 1 = 2 ^ (e * r ^ 2) * ∏ j ∈ Icc 1 r, (q ^ (2 * j) - 1) := by
    rw [mul_one, h, hqk]
  have hdiv := exact_pow_of_mul_eq hp (by norm_num) hP h1
  have hr9 : 9 ≤ r ^ 2 := by nlinarith
  refine ⟨hp, ⟨e * r ^ 2, by nlinarith, hdiv.1, hdiv.2, ?_⟩, fun h2 => absurd rfl h2, fun _ => ?_⟩
  · calc M ^ 2 < (q ^ (2 * r ^ 2 + r)) ^ 2 := Nat.pow_lt_pow_left hMlt (by norm_num)
      _ = q ^ (2 * (2 * r ^ 2 + r)) := by rw [← pow_mul, mul_comm]
      _ ≤ q ^ (5 * r ^ 2) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = (2 ^ (e * r ^ 2)) ^ 5 := by rw [mul_comm 5 (r ^ 2), pow_mul, hqk]
  · have hP' : Odd (∏ j ∈ Icc 1 r, ((2 ^ e) ^ (2 * j) - 1)) :=
      odd_prod fun j hj => odd_pow_sub_one (by omega) (by have := (mem_Icc.mp hj).1; omega)
    refine ⟨fun k => ∃ i ∈ Icc 1 r, k ∣ e * (2 * i), e * (r * r), e * (2 * r), ?_, ?_,
      by nlinarith, Nat.mul_lt_mul_of_pos_left (by nlinarith) (by omega)⟩
    · refine Profile.of_eq ?_ hP' fun p' k hp' hk => ?_
      · rw [h, ← pow_mul, sq]
      · rw [(Nat.Prime.prime hp'.prime).dvd_finsetProd_iff]
        exact exists_congr fun i => and_congr_right fun _ =>
          PrimDiv.dvd_pow_sub_one_iff hp' hk e _
    · rintro k ⟨i, hi, hk⟩
      simp only [mem_Icc] at hi
      exact (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hk).trans
        (Nat.mul_le_mul_left _ (by omega))

theorem xinfo_of_xord {M p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (h : XOrd M p e) :
    XInfo M p e := by
  cases h with
  | sl n g hn hg h => exact xinfo_sl hp he hn hg h
  | spOdd r hr hp2 h => exact xinfo_spOdd hp he hr hp2 h
  | spEven r hr hp2 h =>
    subst hp2
    exact xinfo_spEven he hr h

end CFSG.RankThree.PartTwo.Sec4.HeringPin
