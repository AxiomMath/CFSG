module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

namespace OrdPOutSU

open CFSG.Timmesfeld Finset CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem uFactor_eq (f j : ℕ) :
    ((2 ^ f : ℕ) : ℤ) ^ j - (-1) ^ j =
      if Even j then ((2 ^ (f * j) - 1 : ℕ) : ℤ) else ((2 ^ (f * j) + 1 : ℕ) : ℤ) := by
  split_ifs with hj
  · rw [hj.neg_one_pow, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  · rw [(Nat.not_even_iff_odd.mp hj).neg_one_pow]
    push_cast
    ring

theorem dvd_uFactor_iff {r k : ℕ} (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k) (f j : ℕ) :
    (r : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ j - (-1) ^ j ↔
      (Even j ∧ k ∣ f * j) ∨ (¬ Even j ∧ k ∣ 2 * (f * j) ∧ ¬ k ∣ f * j) := by
  rw [uFactor_eq]
  split_ifs with hj
  · rw [Int.natCast_dvd_natCast, hr.dvd_sub_one_iff hk]
    tauto
  · rw [Int.natCast_dvd_natCast, hr.dvd_add_one_iff hk]
    tauto

theorem lt_of_ppd {r k : ℕ} (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k) : k < r := by
  have hr2 := hr.ne_two hk
  have : Fact r.Prime := ⟨hr.prime⟩
  have h : r ∣ 2 ^ (r - 1) - 1 :=
    (Bang.dvd_two_pow_sub_one_iff (r - 1)).mpr
      (ZMod.pow_card_sub_one_eq_one (Bang.two_ne_zero_zmod hr2))
  have h1 := (hr.dvd_sub_one_iff hk (r - 1)).mp h
  have hr1 : 0 < r - 1 := by have := hr.prime.two_le; omega
  have := Nat.le_of_dvd hr1 h1
  omega

structure IsUnitaryPPD (r f n : ℕ) : Prop where
  prime : r.Prime
  dvd : (r : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ n - (-1) ^ n
  not_dvd : ∀ j, 0 < j → j < n → ¬ (r : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ j - (-1) ^ j
  lt : 2 * f < r

theorem exists_isUnitaryPPD {f n : ℕ} (hf : 1 ≤ f) (hn : 3 ≤ n) (h3 : ¬ (n = 3 ∧ f = 1))
    (h6 : ¬ (n = 6 ∧ f = 2)) : ∃ r, IsUnitaryPPD r f n := by
  rcases Nat.even_or_odd n with ⟨n', hn'⟩ | hno
  · rcases Nat.even_or_odd n' with ⟨n'', hn''⟩ | ho'
    ·
      have hn4 : n = 4 * n'' := by omega
      have hk : 0 < f * n := Nat.mul_pos (by omega) (by omega)
      have hfn : f * n = 4 * (f * n'') := by rw [hn4]; ring
      obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := f * n) (by omega) (by omega)
      refine ⟨r, hr.prime, (dvd_uFactor_iff hr hk f n).mpr (Or.inl ⟨⟨n', hn'⟩, dvd_rfl⟩),
        fun j hj0 hjn hd => ?_, ?_⟩
      · rcases (dvd_uFactor_iff hr hk f j).mp hd with ⟨-, hd⟩ | ⟨hjo, hd, -⟩
        · have := Nat.le_of_dvd hj0 (Nat.dvd_of_mul_dvd_mul_left (by omega) hd)
          omega
        · obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f)
            (show f * n ∣ f * (2 * j) by rw [mul_left_comm]; exact hd)
          exact hjo ⟨n'' * t, by rw [hn4] at ht; linarith⟩
      · have := lt_of_ppd hr hk
        have : 2 * f < f * n := by nlinarith [Nat.mul_le_mul_left f (show 4 ≤ n by omega)]
        omega
    ·
      obtain ⟨t, ht⟩ := ho'
      have hn3 : 3 ≤ n' := by omega
      have hk : 0 < f * n' := Nat.mul_pos (by omega) (by omega)
      have hcop : Nat.Coprime 2 n' := (Nat.coprime_two_left).mpr ⟨t, ht⟩
      have hk6 : f * n' ≠ 6 := by
        intro h
        have hf2 : f ≤ 2 := by nlinarith
        interval_cases f <;> omega
      obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := f * n') (by nlinarith) hk6
      refine ⟨r, hr.prime, (dvd_uFactor_iff hr hk f n).mpr (Or.inl ⟨⟨n', hn'⟩,
        ⟨2, by rw [hn']; ring⟩⟩), fun j hj0 hjn hd => ?_, ?_⟩
      · rcases (dvd_uFactor_iff hr hk f j).mp hd with ⟨hje, hd⟩ | ⟨-, hd, hnd⟩
        · have h1 := Nat.dvd_of_mul_dvd_mul_left (by omega) hd
          have h2 : 2 * n' ∣ j := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp hje) h1
          have := Nat.le_of_dvd hj0 h2
          omega
        · have h1 := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < f)
            (show f * n' ∣ f * (2 * j) by rw [mul_left_comm]; exact hd)
          exact hnd (Nat.mul_dvd_mul_left f (hcop.symm.dvd_of_dvd_mul_left h1))
      · have := lt_of_ppd hr hk
        have : 2 * f < f * n' := by nlinarith
        omega
  ·
    have hfn : 0 < f * n := Nat.mul_pos (by omega) (by omega)
    have hk : 0 < 2 * (f * n) := Nat.mul_pos two_pos hfn
    have hk6 : 2 * (f * n) ≠ 6 := by
      intro h
      have h' : f * n = 3 := by omega
      have hf1 : f = 1 := by
        by_contra hf1
        have : 2 * n ≤ f * n := Nat.mul_le_mul_right n (by omega)
        omega
      subst hf1
      exact h3 ⟨by omega, rfl⟩
    obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * (f * n)) (by omega) hk6
    refine ⟨r, hr.prime, (dvd_uFactor_iff hr hk f n).mpr (Or.inr ⟨Nat.not_even_iff_odd.mpr hno,
      dvd_rfl, fun h => by have := Nat.le_of_dvd hfn h; omega⟩), fun j hj0 hjn hd => ?_, ?_⟩
    · have hfj : f * j < f * n := Nat.mul_lt_mul_of_pos_left hjn (by omega)
      rcases (dvd_uFactor_iff hr hk f j).mp hd with ⟨-, hd⟩ | ⟨-, hd, -⟩
      · have := Nat.le_of_dvd (Nat.mul_pos (by omega) hj0) hd
        omega
      · have := Nat.le_of_dvd (Nat.mul_pos two_pos (Nat.mul_pos (by omega) hj0)) hd
        omega
    · have := lt_of_ppd hr hk
      have : 2 * f < 2 * (f * n) := by nlinarith
      omega

namespace IsUnitaryPPD

variable {r f n : ℕ}

theorem ne_two (h : IsUnitaryPPD r f n) (hf : 1 ≤ f) : r ≠ 2 := by
  have := h.lt
  omega

theorem not_dvd_two_pow_add_one (h : IsUnitaryPPD r f n) (hn : 1 < n) : ¬ r ∣ 2 ^ f + 1 := by
  intro hd
  apply h.not_dvd 1 one_pos hn
  rw [pow_one, pow_one, sub_neg_eq_add]
  exact_mod_cast hd

theorem not_dvd_sq_sub_one (h : IsUnitaryPPD r f n) (hn : 2 < n) : ¬ r ∣ (2 ^ f) ^ 2 - 1 := by
  intro hd
  apply h.not_dvd 2 two_pos hn
  have e : ((((2 ^ f) ^ 2 - 1 : ℕ)) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by positivity))]
    push_cast
    ring
  rw [← e]
  exact_mod_cast hd

theorem dvd_pow_sub (h : IsUnitaryPPD r f n) {p m : ℕ} (hp : Odd p) (hnpm : p * m = n) :
    (r : ℤ) ∣ ((2 ^ (f * p) : ℕ) : ℤ) ^ m - (-1) ^ m := by
  have e1 : ((2 ^ (f * p) : ℕ) : ℤ) ^ m = ((2 ^ f : ℕ) : ℤ) ^ n := by
    rw [← hnpm]
    push_cast
    ring
  have e2 : ((-1 : ℤ)) ^ m = (-1) ^ n := by
    rw [← hnpm, pow_mul, hp.neg_one_pow]
  rw [e1, e2]
  exact h.dvd

theorem not_dvd_card_unitarySU (h : IsUnitaryPPD r f n) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : UnitaryFieldData 2 f K) {k : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    ¬ r ∣ Nat.card (unitarySU 2 f K k) := by
  have : CharP K 2 := hK.charP
  have hU := (CFSG.LinearGroups.unitary_full_group_order hK
    (gramForm_isSymm hK (G := (1 : Matrix (Fin k) (Fin k) K)) (by simp))
    (gramForm_separatingLeft hK (by simp)) (Module.finrank_fin_fun K) hk).2.1
  have hcard : (Nat.card (unitarySU 2 f K k) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [unitarySU_eq_gramSU hK, card_gramSU, hU]
  intro hd
  have hd' : (r : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) :=
    hcard ▸ Int.natCast_dvd_natCast.mpr hd
  have hrp : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp h.prime
  rcases hrp.dvd_or_dvd hd' with h1 | h1
  · have h2 : r ∣ 2 ^ f := Int.natCast_dvd_natCast.mp (hrp.dvd_of_dvd_pow h1)
    exact h.ne_two hf ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (h.prime.dvd_of_dvd_pow h2))
  · obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hrp _).mp h1
    rw [Finset.mem_Icc] at hi
    exact h.not_dvd i (by omega) (by omega) hdi

end IsUnitaryPPD

theorem mul_dvd_pow_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) :
    p * (q + 1) ∣ q ^ p + 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set S : ℤ := ∑ i ∈ range p, (q : ℤ) ^ i * (-1) ^ (p - 1 - i) with hS
  have hmul : S * ((q : ℤ) + 1) = (q : ℤ) ^ p + 1 := by
    have := geom_sum₂_mul (q : ℤ) (-1) p
    rw [hodd.neg_one_pow, sub_neg_eq_add, sub_neg_eq_add] at this
    exact this
  have hSp : (p : ℤ) ∣ S := by
    have hq : (q : ℤ) ≡ -1 [ZMOD p] := by
      have h1 : (p : ℤ) ∣ (q : ℤ) + 1 := by exact_mod_cast hpq
      have h2 : (-1 : ℤ) - q = -((q : ℤ) + 1) := by ring
      exact (Int.modEq_iff_dvd.mpr (h2 ▸ (dvd_neg).mpr h1))
    have hterm : ∀ i ∈ range p, ((-1 : ℤ)) ^ i * (-1) ^ (p - 1 - i) = 1 := by
      intro i hi
      rw [← pow_add, show i + (p - 1 - i) = p - 1 by have := mem_range.mp hi; omega]
      exact (Nat.Odd.sub_odd hodd odd_one).neg_one_pow
    have hmod : S ≡ ∑ i ∈ range p, ((-1 : ℤ)) ^ i * (-1) ^ (p - 1 - i) [ZMOD p] :=
      Int.ModEq.sum fun i _ => (hq.pow i).mul_right _
    rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul, mul_one] at hmod
    have h3 := Int.ModEq.dvd hmod.symm
    have h4 : (p : ℤ) ∣ S - p + p := dvd_add h3 dvd_rfl
    simpa using h4
  obtain ⟨t, ht⟩ := hSp
  have e : ((q ^ p + 1 : ℕ) : ℤ) = ((p * (q + 1) : ℕ) : ℤ) * t := by
    push_cast
    rw [← hmul, ht]
    ring
  exact Int.natCast_dvd_natCast.mp ⟨t, e⟩

end OrdPOutSU

end CFSG.StandardType
