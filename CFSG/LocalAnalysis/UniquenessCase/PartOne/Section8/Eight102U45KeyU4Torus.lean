module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs
public import CFSG.Milestones.ASVolI.F431.BCoreU4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem factorization_card_hypSU_two_zero_of_dvd (h : UnitaryFieldData 2 n K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    (Nat.card (hypSU h 2 0)).factorization p = 2 * (Nat.card Kˣ).factorization p := by
  have hcard : Nat.card (hypSU h 2 0) = (2 ^ n) ^ 6 *
      (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1)) := by
    have h1 := (card_hypSU h (r := 2) (ε := 0) (by norm_num)).1
    have hIcc : Finset.Icc 2 4 = {2, 3, 4} := by decide
    rw [hIcc] at h1
    norm_num at h1
    apply (Nat.cast_inj (R := ℤ)).mp
    have h2pos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow 2 _ (by positivity)
    have h4pos : 1 ≤ (2 ^ n) ^ 4 := Nat.one_le_pow 4 _ (by positivity)
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_sub h2pos, Nat.cast_sub h4pos]
    rw [h1]
    push_cast
    ring
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hq1 : 1 < 2 ^ n := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
  have h2m : (2 ^ n) ^ 2 - 1 ≠ 0 := by
    have h2 : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have h2p : (2 ^ n) ^ 2 + 1 ≠ 0 := by positivity
  have h3p : (2 ^ n) ^ 3 + 1 ≠ 0 := by positivity
  have h4n : (2 ^ n) ^ 4 - 1 ≠ 0 := by
    have h4 : 1 < (2 ^ n) ^ 4 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hnot : ∀ j : ℕ, ¬ p ∣ (2 ^ n) ^ j + 1 := by
    intro j hd
    have h1 : p ∣ (2 ^ n) ^ j - 1 :=
      dvd_trans hpn (Nat.sub_one_dvd_pow_sub_one (2 ^ n) j)
    have h2 : 1 ≤ (2 ^ n) ^ j := Nat.one_le_pow j _ (by positivity)
    have hsub := Nat.dvd_sub hd h1
    rw [show (2 ^ n) ^ j + 1 - ((2 ^ n) ^ j - 1) = 2 by omega] at hsub
    rcases (Nat.dvd_prime Nat.prime_two).mp hsub with h' | h'
    · exact hp.ne_one h'
    · exact hp2 h'
  have hq : ¬ p ∣ 2 ^ n := by
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd) with h' | h'
    · exact hp.ne_one h'
    · exact hp2 h'
  have hq6 : ¬ p ∣ (2 ^ n) ^ 6 := fun hd => hq (hp.dvd_of_dvd_pow hd)
  have h4eq : (2 ^ n) ^ 4 - 1 = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 + 1) := by
    have hpow : (2 ^ n) ^ 4 = ((2 ^ n) ^ 2) ^ 2 := by ring
    rw [hpow]
    calc ((2 ^ n) ^ 2) ^ 2 - 1 = ((2 ^ n) ^ 2) ^ 2 - 1 ^ 2 := by norm_num
      _ = ((2 ^ n) ^ 2 + 1) * ((2 ^ n) ^ 2 - 1) := Nat.sq_sub_sq _ _
      _ = ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 2 + 1) := by ring
  have h4fac : ((2 ^ n) ^ 4 - 1).factorization p = ((2 ^ n) ^ 2 - 1).factorization p := by
    rw [h4eq, Nat.factorization_mul h2m h2p, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (hnot 2), add_zero]
  have hmain : (Nat.card (hypSU h 2 0)).factorization p =
      2 * ((2 ^ n) ^ 2 - 1).factorization p := by
    rw [hcard, Nat.factorization_mul (pow_ne_zero 6 hq0)
        (mul_ne_zero (mul_ne_zero h2m h3p) h4n),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hq6, zero_add,
      Nat.factorization_mul (mul_ne_zero h2m h3p) h4n, Finsupp.add_apply,
      Nat.factorization_mul h2m h3p, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (hnot 3), add_zero, h4fac]
    ring
  have hunits : Nat.card Kˣ = (2 ^ n) ^ 2 - 1 := by
    rw [Nat.card_units, h.card, show 2 * n = n * 2 by omega, pow_mul]
  rw [hmain, hunits]

theorem pow_factorization_card_units_dvd (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) : p ^ (Nat.card Kˣ).factorization p ∣ 2 ^ n - 1 := by
  have hne : 2 ^ n - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ n := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
    omega
  have hnot : ¬ p ∣ 2 ^ n + 1 := by
    intro hd
    have hsub := Nat.dvd_sub hd hpn
    rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega] at hsub
    rcases (Nat.dvd_prime Nat.prime_two).mp hsub with h' | h'
    · exact hp.ne_one h'
    · exact hp2 h'
  have hKcard : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, h.card, show 2 * n = n * 2 by omega, pow_mul, ← Nat.sq_sub_sq,
      one_pow]
  have hfac : (Nat.card Kˣ).factorization p = (2 ^ n - 1).factorization p := by
    rw [hKcard, Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnot, zero_add]
  rw [hfac]
  exact Nat.ordProj_dvd (2 ^ n - 1) p

theorem sylow_torusPow_hypSU_two_zero (h : UnitaryFieldData 2 n K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    IsPGroup p (Syl3.torusPow h 2 0 (p ^ (Nat.card Kˣ).factorization p)) ∧
      ¬ p ∣ (Syl3.torusPow h 2 0 (p ^ (Nat.card Kˣ).factorization p)).index := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hcard : Nat.card (Syl3.torusPow h 2 0 (p ^ (Nat.card Kˣ).factorization p)) =
      p ^ (Nat.card (hypSU h 2 0)).factorization p := by
    rw [Syl3.card_torusPow h 2 0 (pow_factorization_card_units_dvd h hp hp2 hpn),
      factorization_card_hypSU_two_zero_of_dvd h hp hp2 hpn, ← pow_mul, mul_comm]
  exact ⟨(Sylow.ofCard _ hcard).isPGroup', (Sylow.ofCard _ hcard).not_dvd_index⟩

theorem mul_comm_of_mem_torusPow {q f : ℕ} {h : UnitaryFieldData q f K} {r ε m k : ℕ}
    {g g' : hypSU h r ε} (hg : g ∈ Syl3.torusPow h r ε m) (hg' : g' ∈ Syl3.torusPow h r ε k) :
    g * g' = g' * g := by
  have h1 : g ∈ Syl3.torusPow h r ε (m * k) :=
    Syl3.torusPow_le_of_dvd h r ε (dvd_mul_right m k) hg
  have h2 : g' ∈ Syl3.torusPow h r ε (m * k) :=
    Syl3.torusPow_le_of_dvd h r ε (dvd_mul_left k m) hg'
  exact congrArg Subtype.val
    ((Syl3.isElemAbelian_torusPow h r ε (m * k)).1.is_comm.comm ⟨g, h1⟩ ⟨g', h2⟩)

theorem burnsideF4m_U4_fieldAut_pow_apply_of_mem_torusPow (h : UnitaryFieldData 2 n K)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 2) {M k : ℕ} (hMk : M ∣ 2 ^ k - 1)
    {g : hypSU h 2 0} (hg : g ∈ Syl3.torusPow h 2 0 M) :
    (ASVolI.burnsideF4m_U4_fieldAut h σ ^ k) g = g := by
  obtain ⟨a, ha, hmat⟩ := Syl3.mem_torusPow.mp hg
  have hM : ∀ x : HypIndex 2 0, torusEntries h a 1 x ^ M = 1 := by
    intro x
    rcases x with i | j | i
    · simpa [torusEntries, Units.val_pow_eq_pow_val] using congrArg Units.val (ha i)
    · exact j.elim0
    · have haK : (a i : K) ^ M = 1 := by
        simpa [Units.val_pow_eq_pow_val] using congrArg Units.val (ha i)
      have hb : (h.bar (a i : K)) ^ M = 1 := by rw [← map_pow, haK, map_one]
      simp [torusEntries, inv_pow, hb]
  have hroot : ∀ x : HypIndex 2 0, torusEntries h a 1 x ^ 2 ^ k = torusEntries h a 1 x := by
    intro x
    obtain ⟨c, hc⟩ := hMk
    have h2k : 2 ^ k = M * c + 1 := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      omega
    rw [h2k, pow_succ, pow_mul, hM x, one_pow, one_mul]
  have hpow : ASVolI.burnsideF4m_U4_fieldAut h σ ^ k =
      ASVolI.burnsideF4m_U4_fieldAut h (σ ^ k) :=
    (map_pow (ASVolI.burnsideF4m_U4_fieldAut h) σ k).symm
  rw [hpow]
  apply Subtype.ext
  apply Units.ext
  rw [show ASVolI.burnsideF4m_U4_fieldAut h (σ ^ k) g =
      ASVolI.burnsideF4m_U4_fieldElt h (σ ^ k) g from rfl,
    ASVolI.burnsideF4m_U4_coe_fieldElt,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut, hmat,
    Matrix.diagonal_map (map_zero (σ ^ k)), Matrix.diagonal_eq_diagonal_iff]
  intro x
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.pow_apply_of_frobenius hσ k]
  exact hroot x

theorem three_pow_factorization_dvd_two_pow_sub_one (h : UnitaryFieldData 2 n K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {a m : ℕ} (hnm : 2 * n = p ^ a * m) :
    3 ^ (Nat.card Kˣ).factorization 3 ∣ 2 ^ m - 1 := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have h2pa : ¬ 2 ∣ p ^ a := by
    intro hd
    rcases (Nat.dvd_prime hp).mp (Nat.prime_two.dvd_of_dvd_pow hd) with h' | h'
    · norm_num at h'
    · exact hp2 h'.symm
  have hm2 : 2 ∣ m := by
    have hdvd : 2 ∣ p ^ a * m := hnm ▸ dvd_mul_right 2 n
    exact (Nat.prime_two.dvd_mul.mp hdvd).resolve_left h2pa
  have hm0 : m ≠ 0 := by
    intro hm
    have h2 : 2 * n = 0 := by rw [hnm, hm, Nat.mul_zero]
    exact (Nat.one_le_iff_ne_zero.mp h.one_le)
      ((Nat.mul_eq_zero.mp h2).resolve_left (by norm_num))
  have h3pa : ¬ 3 ∣ p ^ a := by
    intro hd
    rcases (Nat.dvd_prime hp).mp (Nat.prime_three.dvd_of_dvd_pow hd) with h' | h'
    · norm_num at h'
    · exact hp3 h'.symm
  have hmj : m = 2 * (m / 2) := (Nat.mul_div_cancel' hm2).symm
  have hx3 : ((2 ^ m : ℕ) : ZMod 3) = 1 := by
    have h4 : ((4 : ℕ) : ZMod 3) = 1 := by decide
    rw [hmj, pow_mul, Nat.cast_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, h4, one_pow]
  have hGz : (((∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i : ℕ)) : ZMod 3) = (p ^ a : ℕ) := by
    calc (((∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i : ℕ)) : ZMod 3)
        = ∑ i ∈ Finset.range (p ^ a), ((2 ^ m : ℕ) : ZMod 3) ^ i := by
          rw [Nat.cast_sum]
          simp only [Nat.cast_pow]
      _ = ∑ i ∈ Finset.range (p ^ a), (1 : ZMod 3) ^ i :=
          Finset.sum_congr rfl fun i _ => by rw [hx3]
      _ = ∑ _i ∈ Finset.range (p ^ a), (1 : ZMod 3) := by simp
      _ = (p ^ a : ℕ) := by simp
  have h3G : ¬ 3 ∣ ∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i := by
    intro hd
    have h0 : (((∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i : ℕ)) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff _ 3).mpr hd
    rw [hGz] at h0
    exact h3pa ((ZMod.natCast_eq_zero_iff _ 3).mp h0)
  have hx1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
  have hgeom : (∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i) * (2 ^ m - 1) + 1 =
      (2 ^ m) ^ (p ^ a) := by
    have h := geom_sum_mul_add (2 ^ m - 1) (p ^ a)
    rwa [Nat.sub_add_cancel hx1] at h
  have hxd : (2 ^ m) ^ (p ^ a) - 1 =
      (∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i) * (2 ^ m - 1) :=
    (Nat.eq_sub_of_add_eq hgeom).symm
  have hGne : (∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i) ≠ 0 := by
    have hpos : 0 < ∑ i ∈ Finset.range (p ^ a), (2 ^ m) ^ i :=
      Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.mpr hpa⟩
    omega
  have hxne : 2 ^ m - 1 ≠ 0 := by
    have h2 : 1 < 2 ^ m := Nat.one_lt_pow hm0 (by norm_num)
    omega
  have hK : Nat.card Kˣ = (2 ^ m) ^ (p ^ a) - 1 := by
    rw [Nat.card_units, h.card, hnm, pow_mul']
  have hfac : (Nat.card Kˣ).factorization 3 = (2 ^ m - 1).factorization 3 := by
    rw [hK, hxd, Nat.factorization_mul hGne hxne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3G, zero_add]
  rw [hfac]
  exact Nat.ordProj_dvd (2 ^ m - 1) 3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
