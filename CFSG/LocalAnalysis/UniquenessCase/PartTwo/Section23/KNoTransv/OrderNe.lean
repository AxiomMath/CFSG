module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.OrderPerm
import CFSG.Quasithin.Recognition.F112Crit.McLOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon
open CFSG.Timmesfeld
open CFSG.Quasithin.F112Crit.McLOrd

private lemma le_succ_of_two_pow_dvd {A N c r : ℕ} (hr : Odd r) (hc : c = 1 ∨ c = 2)
    (h : 2 ^ A ∣ (2 ^ N * r) * c) : A ≤ N + 1 := by
  have h' : 2 ^ A ∣ 2 ^ (N + 1) * r := by
    rcases hc with rfl | rfl
    · have h1 : 2 ^ A ∣ 2 ^ N * r := by simpa using h
      exact h1.trans (mul_dvd_mul_right (Nat.pow_dvd_pow 2 (Nat.le_succ N)) r)
    · rw [mul_assoc, mul_comm r 2, ← mul_assoc, ← pow_succ] at h
      exact h
  exact le_of_two_pow_dvd hr h'

private lemma false_of_ordData_SL {m c N E p r n : ℕ} (hr : Odd r) (hc : c = 1 ∨ c = 2)
    (hmr : m = 2 ^ N * r) (hpm : p ∣ m) (hp : IsPrimitivePrimeDivisor p E) (hE7 : 7 ≤ E)
    (h2N : 2 * N ≤ 3 * E) (hn : 2 ≤ n)
    (hmc : m * c = 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1)) : False := by
  have hA : n * (n - 1) / 2 ≤ N + 1 := by
    refine le_succ_of_two_pow_dvd hr hc ?_
    rw [← hmr, hmc]
    exact dvd_mul_right _ _
  have hpW : p ∣ 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
    rw [← hmc]
    exact dvd_mul_of_dvd_left hpm c
  have hpP : p ∣ ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) :=
    dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two (by omega)) hpW
  obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp hpP
  have hj' := Finset.mem_Icc.mp hj
  have hEj : E ∣ j := (hp.dvd_sub_one_iff (by omega) j).mp hpj
  have hEn : E ≤ n := (Nat.le_of_dvd (by omega) hEj).trans hj'.2
  have hn4 : n ≤ 4 := by
    have h1 : n * (n - 1) ≤ 2 * (N + 1) + 1 :=
      (Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)).mp hA
    have h2N' : 2 * N ≤ 3 * n := le_trans h2N (Nat.mul_le_mul_left 3 hEn)
    by_contra h
    have h5 : 5 ≤ n := by omega
    have h4 : 4 * n ≤ n * (n - 1) := by
      rw [mul_comm 4 n]
      exact Nat.mul_le_mul_left n (by omega)
    omega
  omega

private lemma false_of_ordData_Sp {m c N E p r n : ℕ} (hr : Odd r) (hc : c = 1 ∨ c = 2)
    (hmr : m = 2 ^ N * r) (hpm : p ∣ m) (hp : IsPrimitivePrimeDivisor p E) (hE7 : 7 ≤ E)
    (h2N : 2 * N ≤ 3 * E) (hn : 2 ≤ n)
    (hmc : m * c = 2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1)) : False := by
  have hA : n ^ 2 ≤ N + 1 := by
    refine le_succ_of_two_pow_dvd hr hc ?_
    rw [← hmr, hmc]
    exact dvd_mul_right _ _
  have hpW : p ∣ 2 ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) := by
    rw [← hmc]
    exact dvd_mul_of_dvd_left hpm c
  have hpP : p ∣ ∏ j ∈ Finset.Icc 1 n, (2 ^ (2 * j) - 1) :=
    dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two (by omega)) hpW
  obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp hpP
  have hj' := Finset.mem_Icc.mp hj
  have hEj : E ∣ 2 * j := (hp.dvd_sub_one_iff (by omega) (2 * j)).mp hpj
  have hEn : E ≤ 2 * n := (Nat.le_of_dvd (by omega) hEj).trans (Nat.mul_le_mul_left 2 hj'.2)
  have hn3 : n ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ n := by omega
    nlinarith
  omega

private lemma false_of_ordData_OPlus {m c N E p r k : ℕ} (hr : Odd r) (hc : c = 1 ∨ c = 2)
    (hmr : m = 2 ^ N * r) (hpm : p ∣ m) (hp : IsPrimitivePrimeDivisor p E) (hE7 : 7 ≤ E)
    (h2N : 2 * N ≤ 3 * E) (hk : 1 ≤ k)
    (hmc : m * c = 2 * 2 ^ (k * (k + 1)) * (2 ^ (k + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1)) : False := by
  have hw : 2 * 2 ^ (k * (k + 1)) * (2 ^ (k + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1) =
      2 ^ (k * (k + 1) + 1) * ((2 ^ (k + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1)) := by
    ring
  have hA : k * (k + 1) + 1 ≤ N + 1 := by
    refine le_succ_of_two_pow_dvd hr hc ?_
    rw [← hmr, hmc, hw]
    exact dvd_mul_right _ _
  have hkN : k * (k + 1) ≤ N := by omega
  have hpW : p ∣ 2 ^ (k * (k + 1) + 1) * ((2 ^ (k + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1)) := by
    rw [← hw, ← hmc]
    exact dvd_mul_of_dvd_left hpm c
  have hpP : p ∣ (2 ^ (k + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1) :=
    dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two (by omega)) hpW
  have hEk : E ≤ 2 * k := by
    rcases hp.prime.dvd_mul.mp hpP with h | h
    · have h1 : E ∣ k + 1 := (hp.dvd_sub_one_iff (by omega) (k + 1)).mp h
      have := Nat.le_of_dvd (by omega) h1
      omega
    · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp h
      have hi' := Finset.mem_Icc.mp hi
      have h1 : E ∣ 2 * i := (hp.dvd_sub_one_iff (by omega) (2 * i)).mp hpi
      have := Nat.le_of_dvd (by omega) h1
      omega
  have hk2 : k ≤ 2 := by
    have hN : N ≤ 3 * k := by omega
    have h : k * (k + 1) ≤ k * 3 := by
      calc k * (k + 1) ≤ N := hkN
        _ ≤ 3 * k := hN
        _ = k * 3 := by ring
    have := Nat.le_of_mul_le_mul_left h (by omega : 0 < k)
    omega
  omega

private lemma false_of_ordData_OMinus {m c N E p r n : ℕ} (hr : Odd r) (hc : c = 1 ∨ c = 2)
    (hmr : m = 2 ^ N * r) (hpm : p ∣ m) (hp : IsPrimitivePrimeDivisor p E) (hE7 : 7 ≤ E)
    (h2N : 2 * N ≤ 3 * E) (h2N9 : 2 * N = 3 * E → 9 ≤ E) (hn : 1 ≤ n)
    (hmc : m * c = 2 * 2 ^ (n * (n + 1)) * (2 ^ (n + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1)) : False := by
  have hw : 2 * 2 ^ (n * (n + 1)) * (2 ^ (n + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1) =
      2 ^ (n * (n + 1) + 1) * ((2 ^ (n + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1)) := by
    ring
  have hA : n * (n + 1) + 1 ≤ N + 1 := by
    refine le_succ_of_two_pow_dvd hr hc ?_
    rw [← hmr, hmc, hw]
    exact dvd_mul_right _ _
  have hnN : n * (n + 1) ≤ N := by omega
  have hpW : p ∣ 2 ^ (n * (n + 1) + 1) * ((2 ^ (n + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1)) := by
    rw [← hw, ← hmc]
    exact dvd_mul_of_dvd_left hpm c
  have hpP : p ∣ (2 ^ (n + 1) + 1) *
      ∏ i ∈ Finset.Icc 1 n, (2 ^ (2 * i) - 1) :=
    dvd_of_dvd_two_pow_mul hp.prime (hp.ne_two (by omega)) hpW
  have hEn : E ≤ 2 * n + 2 := by
    rcases hp.prime.dvd_mul.mp hpP with h | h
    · have h2 : p ∣ 2 ^ (2 * (n + 1)) - 1 := by
        rw [IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
        exact dvd_mul_of_dvd_right h _
      have h1 : E ∣ 2 * (n + 1) := (hp.dvd_sub_one_iff (by omega) (2 * (n + 1))).mp h2
      have := Nat.le_of_dvd (by omega) h1
      omega
    · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime.prime _).mp h
      have hi' := Finset.mem_Icc.mp hi
      have h1 : E ∣ 2 * i := (hp.dvd_sub_one_iff (by omega) (2 * i)).mp hpi
      have := Nat.le_of_dvd (by omega) h1
      omega
  have hn3 : n ≤ 3 := by
    have hN : N ≤ 3 * n + 3 := by omega
    by_contra h
    have h4 : 4 ≤ n := by omega
    nlinarith
  obtain rfl : n = 3 := by omega
  have hN : N = 12 := by
    have h1 : 12 ≤ N := by simpa using hnN
    omega
  have h2N3E : 2 * N = 3 * E := by omega
  have := h2N9 h2N3E
  omega

theorem false_of_ordData_of_isMcLaughlinGroup {W : Type} [Group W] [Finite W]
    (hW : UniquenessMaximal.IsMcLaughlinGroup W) {m c : ℕ} (hm : OrdData m) (hc : c = 1 ∨ c = 2)
    (hmc : m * c = Nat.card W) (hperm : ∀ n : ℕ, Nonempty (W ≃* Equiv.Perm (Fin n)) → c = 2) :
    False := by
  have hm0 : OrdData m := hm
  obtain ⟨N, E, p, ⟨r, hr, hmr⟩, hE7, hp, hpm, h2N, h2N9, _⟩ := hm
  rcases hW with ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv, card_statedSL_zmod_two (by omega)] at hmc
    exact false_of_ordData_SL hr hc hmr hpm hp hE7 h2N hn hmc
  · rw [Nat.card_congr φ.toEquiv, card_statedSp_zmod_two] at hmc
    exact false_of_ordData_Sp hr hc hmr hpm hp hE7 h2N hn hmc
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.card_congr φ.toEquiv, card_glaPlus_zmod_two] at hmc
    exact false_of_ordData_OPlus hr hc hmr hpm hp hE7 h2N (by omega) hmc
  · rw [Nat.card_congr φ.toEquiv, card_glaMinus_zmod_two] at hmc
    exact false_of_ordData_OMinus hr hc hmr hpm hp hE7 h2N h2N9 hn hmc
  · have hc2 : c = 2 := hperm n ⟨φ⟩
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hmc
    exact false_of_ordData_factorial hm0 (by rw [hc2] at hmc; exact hmc)

theorem false_of_card_504_of_isMcLaughlinGroup {W : Type} [Group W] [Finite W]
    (hW : UniquenessMaximal.IsMcLaughlinGroup W) {c : ℕ} (hc : c = 1 ∨ c = 2)
    (hmc : 504 * c = Nat.card W) : False := by
  obtain ⟨-, -, -, h504, h1008⟩ := mcLArith_of_isMcLaughlinGroup hW
  rcases hc with rfl | rfl
  · exact h504 (by simpa using hmc.symm)
  · exact h1008 (by simpa using hmc.symm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
