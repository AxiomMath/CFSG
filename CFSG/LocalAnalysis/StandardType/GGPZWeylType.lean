module

public import CFSG.LocalAnalysis.StandardType.GGPZWeylB
public import CFSG.LocalAnalysis.StandardType.GGPZWeylD
public import CFSG.LocalAnalysis.StandardType.GGPZWeylExc
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.LocalAnalysis.StandardType.GGSpFrameCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSpJoinCoxeterCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGTWTwA5Datum
public import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.StandardType

open CFSG

theorem ggCoxeterA_center (n : ℕ) (hn : 2 ≤ n) :
    Nat.card ↥(Subgroup.center (CoxeterMatrix.A n).Group) = 1 := by
  obtain ⟨e, -⟩ := ggCoxeterA_mulEquivPerm n
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    CFSG.center_perm_eq_bot_of_three_le_card (by simp; omega : 3 ≤ Nat.card (Fin (n + 1)))]
  simp

theorem ggCoxeterA_one_center : Nat.card ↥(Subgroup.center (CoxeterMatrix.A 1).Group) = 2 := by
  obtain ⟨e, -⟩ := ggCoxeterA_mulEquivPerm 1
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  have hcomm : ∀ g h : Equiv.Perm (Fin (1 + 1)), h * g = g * h := by decide
  have htop : Subgroup.center (Equiv.Perm (Fin (1 + 1))) = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun g => Subgroup.mem_center_iff.mpr fun h => hcomm g h
  rw [htop, Subgroup.card_top, Nat.card_perm]
  simp

theorem ggWeylTypeData_of_isWeylMatrix
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) :
    GGWeylTypeData (Fintype.card ι) (Nat.card M.Group)
      (Nat.card ↥(Subgroup.center M.Group)) := by
  have key : ∀ {n : ℕ} (e : Fin n ≃ ι) {M0 : CoxeterMatrix (Fin n)}, M = M0.reindex e →
      GGWeylTypeData n (Nat.card M0.Group) (Nat.card ↥(Subgroup.center M0.Group)) →
      GGWeylTypeData (Fintype.card ι) (Nat.card M.Group)
        (Nat.card ↥(Subgroup.center M.Group)) := by
    intro n e M0 hMe h
    subst hMe
    have h1 : Fintype.card ι = n := by simpa using (Fintype.card_congr e).symm
    have h2 : Nat.card (M0.reindex e).Group = Nat.card M0.Group :=
      Nat.card_congr (M0.reindexGroupEquiv e).toEquiv
    have h3 : Nat.card ↥(Subgroup.center (M0.reindex e).Group) =
        Nat.card ↥(Subgroup.center M0.Group) :=
      Nat.card_congr (Subgroup.centerCongr (M0.reindexGroupEquiv e)).toEquiv
    rw [h1, h2, h3]
    exact h
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ | ⟨e, hE⟩ |
      ⟨e, hE⟩ | ⟨e, hE⟩
  · refine key e hA (Or.inl ⟨hn, l05nK3a_card_coxeterA n, ?_⟩)
    by_cases h1 : n = 1
    · subst h1
      simp [ggCoxeterA_one_center]
    · simp [h1, ggCoxeterA_center n (by omega)]
  · exact key e hB (Or.inr (Or.inl ⟨hn2, by
      rw [le_antisymm (card_coxeterB_le n) (SpFrame.card_coxeterB_ge n hn2)],
      ggCoxeterB_center n hn2⟩))
  · exact key e hD (Or.inr (Or.inr (Or.inl ⟨hn4, OrthF3.card_coxeterD_eq n hn4,
      by rw [ggCoxeterD_center n hn4]⟩)))
  · exact key e hE (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, l05nQW_ord_coxeterE6,
      ggCoxeterE6_center⟩))))
  · exact key e hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, l05nQW_ord_coxeterE7,
      ggCoxeterE7_center⟩)))))
  · exact key e hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, l05nQW_ord_coxeterE8,
      ggCoxeterE8_center⟩))))))
  · exact key e hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
      l04fFRC_ord_card_coxeterF4, ggCoxeterF4_center⟩)))))))
  · exact key e hE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,
      l04fFRC_card_coxeterG2, ggCoxeterG2_center⟩)))))))

theorem ggWeylTypeB_order_le {r s : ℕ} (h : r ≤ s) :
    2 ^ r * r.factorial ≤ 2 ^ s * s.factorial :=
  Nat.mul_le_mul (Nat.pow_le_pow_of_le (by norm_num : 1 < 2) h) (Nat.factorial_le h)

theorem ggWeylTypeB_order_lt {r s : ℕ} (h : r < s) :
    2 ^ r * r.factorial < 2 ^ s * s.factorial := by
  have hpow : 2 ^ r < 2 ^ s := Nat.pow_lt_pow_of_lt (by norm_num : 1 < 2) h
  have hfac : r.factorial ≤ s.factorial := Nat.factorial_le h.le
  calc
    2 ^ r * r.factorial < 2 ^ s * r.factorial :=
      Nat.mul_lt_mul_of_pos_right hpow (Nat.factorial_pos r)
    _ ≤ 2 ^ s * s.factorial := Nat.mul_le_mul_left _ hfac

theorem ggWeylTypeD_order_le {r s : ℕ} (h : r ≤ s) :
    2 ^ (r - 1) * r.factorial ≤ 2 ^ (s - 1) * s.factorial :=
  Nat.mul_le_mul (Nat.pow_le_pow_of_le (by norm_num : 1 < 2) (by omega)) (Nat.factorial_le h)

theorem ggWeylTypeD_order_lt {r s : ℕ} (hr : 4 ≤ r) (h : r < s) :
    2 ^ (r - 1) * r.factorial < 2 ^ (s - 1) * s.factorial := by
  have hpow : 2 ^ (r - 1) < 2 ^ (s - 1) :=
    Nat.pow_lt_pow_of_lt (by norm_num : 1 < 2) (by omega)
  have hfac : r.factorial ≤ s.factorial := Nat.factorial_le h.le
  calc
    2 ^ (r - 1) * r.factorial < 2 ^ (s - 1) * r.factorial :=
      Nat.mul_lt_mul_of_pos_right hpow (Nat.factorial_pos r)
    _ ≤ 2 ^ (s - 1) * s.factorial := Nat.mul_le_mul_left _ hfac

theorem not_ascFactorial_eq_two_pow {n k e : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    n.ascFactorial k ≠ 2 ^ e := by
  intro h
  have hdvd : ∃ m, Odd m ∧ 3 ≤ m ∧ m ∣ n.ascFactorial k := by
    rw [Nat.ascFactorial_eq_prod_range n k]
    rcases Nat.even_or_odd n with he | ho
    · refine ⟨n + 1, he.add_one, by omega, ?_⟩
      exact Finset.dvd_prod_of_mem (fun i => n + i) (a := 1) (by
        rw [Finset.mem_range]
        omega)
    · refine ⟨n, ho, hn, ?_⟩
      exact Finset.dvd_prod_of_mem (fun i => n + i) (a := 0) (by
        rw [Finset.mem_range]
        omega)
  obtain ⟨m, hmodd, _hm3, hmdvd⟩ := hdvd
  have hm_dvd_pow : m ∣ 2 ^ e := by simpa [h] using hmdvd
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hpdvd : p ∣ 2 ^ e := hpm.trans hm_dvd_pow
  have hp_dvd_two : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hpdvd
  have hp_two : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two
  exact (Odd.ne_two_of_dvd_nat hmodd hpm) hp_two

theorem ggWeylTypeA_rank_eq_A {r s : ℕ} (hr : 1 ≤ r)
    (h : (r + 1).factorial = (s + 1).factorial) : r = s := by
  have h' : r + 1 = s + 1 :=
    (Nat.factorial_inj (by omega : 1 < r + 1)).mp h
  omega

theorem ggWeylTypeA_rank_eq_B {r s : ℕ} (hs : 2 ≤ s)
    (h : (r + 1).factorial = 2 ^ s * s.factorial) : r = s := by
  have hsle : s ≤ r := by
    by_contra hsr
    have h1 : r + 1 ≤ s := by omega
    have hfac : (r + 1).factorial ≤ s.factorial := Nat.factorial_le h1
    have hpow : 1 < 2 ^ s := by
      simpa using Nat.pow_lt_pow_of_lt (by norm_num : 1 < 2) (by omega : 0 < s)
    have hlt : s.factorial < 2 ^ s * s.factorial := by
      have hpos : 0 < s.factorial := Nat.factorial_pos s
      have := Nat.mul_lt_mul_of_pos_left hpow hpos
      simpa [mul_comm] using this
    have hlt' : (r + 1).factorial < 2 ^ s * s.factorial :=
      lt_of_le_of_lt hfac hlt
    omega
  have hfac : s.factorial * (s + 1).ascFactorial (r + 1 - s) = (r + 1).factorial := by
    have hsk : s + (r + 1 - s) = r + 1 := by omega
    have h := Nat.factorial_mul_ascFactorial s (r + 1 - s)
    rwa [hsk] at h
  have hasc : (s + 1).ascFactorial (r + 1 - s) = 2 ^ s := by
    apply Nat.mul_left_cancel (Nat.factorial_pos s)
    rw [hfac, h, mul_comm]
  by_cases hk : r + 1 - s = 1
  · omega
  · have hk2 : 2 ≤ r + 1 - s := by omega
    exact absurd hasc (not_ascFactorial_eq_two_pow (n := s + 1) (k := r + 1 - s)
      (e := s) (by omega) hk2)

theorem ggWeylTypeA_rank_eq_D {r s : ℕ} (hs : 4 ≤ s)
    (h : (r + 1).factorial = 2 ^ (s - 1) * s.factorial) : r = s := by
  have hsle : s ≤ r := by
    by_contra hsr
    have h1 : r + 1 ≤ s := by omega
    have hfac : (r + 1).factorial ≤ s.factorial := Nat.factorial_le h1
    have hpow : 1 < 2 ^ (s - 1) := by
      simpa using Nat.pow_lt_pow_of_lt (by norm_num : 1 < 2) (by omega : 0 < s - 1)
    have hlt : s.factorial < 2 ^ (s - 1) * s.factorial := by
      have hpos : 0 < s.factorial := Nat.factorial_pos s
      have := Nat.mul_lt_mul_of_pos_left hpow hpos
      simpa [mul_comm] using this
    have hlt' : (r + 1).factorial < 2 ^ (s - 1) * s.factorial :=
      lt_of_le_of_lt hfac hlt
    omega
  have hfac : s.factorial * (s + 1).ascFactorial (r + 1 - s) = (r + 1).factorial := by
    have hsk : s + (r + 1 - s) = r + 1 := by omega
    have h := Nat.factorial_mul_ascFactorial s (r + 1 - s)
    rwa [hsk] at h
  have hasc : (s + 1).ascFactorial (r + 1 - s) = 2 ^ (s - 1) := by
    apply Nat.mul_left_cancel (Nat.factorial_pos s)
    rw [hfac, h, mul_comm]
  by_cases hk : r + 1 - s = 1
  · omega
  · have hk2 : 2 ≤ r + 1 - s := by omega
    exact absurd hasc (not_ascFactorial_eq_two_pow (n := s + 1) (k := r + 1 - s)
      (e := s - 1) (by omega) hk2)

theorem ggWeylTypeB_rank_eq_B {r s : ℕ}
    (h : 2 ^ r * r.factorial = 2 ^ s * s.factorial) : r = s := by
  by_cases hle : r ≤ s
  · by_cases heq : r = s
    · exact heq
    · have hlt : r < s := by omega
      have hltprod := ggWeylTypeB_order_lt hlt
      omega
  · have hlt : s < r := by omega
    have hltprod := ggWeylTypeB_order_lt hlt
    omega

theorem ggWeylTypeD_rank_eq_D {r s : ℕ} (hr : 4 ≤ r) (hs : 4 ≤ s)
    (h : 2 ^ (r - 1) * r.factorial = 2 ^ (s - 1) * s.factorial) : r = s := by
  by_cases hle : r ≤ s
  · by_cases heq : r = s
    · exact heq
    · have hlt : r < s := by omega
      have hltprod := ggWeylTypeD_order_lt hr hlt
      omega
  · have hlt : s < r := by omega
    have hltprod := ggWeylTypeD_order_lt hs hlt
    omega

theorem ggWeylTypeB_ne_D {r s : ℕ} (hr : 2 ≤ r) (hs : 4 ≤ s) :
    2 ^ r * r.factorial ≠ 2 ^ (s - 1) * s.factorial := by
  intro h
  by_cases hsr : s ≤ r
  · have hDle : 2 ^ (s - 1) * s.factorial ≤ 2 ^ (r - 1) * r.factorial :=
      ggWeylTypeD_order_le hsr
    have hBlt : 2 ^ (r - 1) * r.factorial < 2 ^ r * r.factorial := by
      have hpow : 2 ^ (r - 1) < 2 ^ r :=
        Nat.pow_lt_pow_of_lt (by norm_num : 1 < 2) (by omega)
      exact Nat.mul_lt_mul_of_pos_right hpow (Nat.factorial_pos r)
    have hlt : 2 ^ (s - 1) * s.factorial < 2 ^ r * r.factorial :=
      lt_of_le_of_lt hDle hBlt
    omega
  · have hsge : r + 1 ≤ s := by omega
    have hDge : 2 ^ r * (r + 1).factorial ≤ 2 ^ (s - 1) * s.factorial := by
      have hpow : 2 ^ r ≤ 2 ^ (s - 1) :=
        Nat.pow_le_pow_of_le (by norm_num : 1 < 2) (by omega)
      have hfac : (r + 1).factorial ≤ s.factorial := Nat.factorial_le hsge
      exact Nat.mul_le_mul hpow hfac
    have hBlt : 2 ^ r * r.factorial < 2 ^ r * (r + 1).factorial := by
      have hfaclt : r.factorial < (r + 1).factorial :=
        Nat.factorial_lt_of_lt (by omega) (by omega)
      exact Nat.mul_lt_mul_of_pos_left hfaclt (by positivity)
    have hlt : 2 ^ r * r.factorial < 2 ^ (s - 1) * s.factorial :=
      lt_of_lt_of_le hBlt hDge
    omega

theorem ggWeylTypeA_rank_le_of_factorial_le {r e : ℕ}
    (h : (r + 1).factorial ≤ e) (he : e ≤ 696729600) : r ≤ 11 := by
  by_contra hr
  have h12 : 12 ≤ r := by omega
  have hfac : (13).factorial ≤ (r + 1).factorial := Nat.factorial_le (by omega)
  have h13 : 696729600 < (13).factorial := by norm_num
  omega

theorem ggWeylTypeB_rank_le_of_order_le {r e : ℕ}
    (h : 2 ^ r * r.factorial ≤ e) (he : e ≤ 696729600) : r ≤ 9 := by
  by_contra hr
  have h10 : 10 ≤ r := by omega
  have hB10 : 2 ^ 10 * (10).factorial = 3715891200 := by norm_num
  have hle : 2 ^ 10 * (10).factorial ≤ 2 ^ r * r.factorial :=
    ggWeylTypeB_order_le h10
  omega

theorem ggWeylTypeD_rank_le_of_order_le {r e : ℕ}
    (h : 2 ^ (r - 1) * r.factorial ≤ e) (he : e ≤ 696729600) : r ≤ 9 := by
  by_contra hr
  have h10 : 10 ≤ r := by omega
  have hD10 : 2 ^ (10 - 1) * (10).factorial = 1857945600 := by norm_num
  have hle : 2 ^ (10 - 1) * (10).factorial ≤ 2 ^ (r - 1) * r.factorial :=
    ggWeylTypeD_order_le h10
  omega

theorem ggWeylTypeData_rank_eq {r n c s d : ℕ}
    (hr : GGWeylTypeData r n c) (hs : GGWeylTypeData s n d) : r = s := by
  rcases hr with hA | hB | hD | hE6 | hE7 | hE8 | hF4 | hG2
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · exact ggWeylTypeA_rank_eq_A hA.1 (by omega)
    · exact ggWeylTypeA_rank_eq_B hB'.1 (by omega)
    · exact ggWeylTypeA_rank_eq_D hD'.1 (by omega)
    · obtain ⟨rfl, rfl, -⟩ := hE6'
      have hEq : (r + 1).factorial = 51840 := by omega
      have hbound : r ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE7'
      have hEq : (r + 1).factorial = 2903040 := by omega
      have hbound : r ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE8'
      have hEq : (r + 1).factorial = 696729600 := by omega
      have hbound : r ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hF4'
      have hEq : (r + 1).factorial = 1152 := by omega
      have hbound : r ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hG2'
      have hEq : (r + 1).factorial = 12 := by omega
      have hbound : r ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · have hsr : s = r := ggWeylTypeA_rank_eq_B (r := s) (s := r) hB.1 (by omega)
      omega
    · exact ggWeylTypeB_rank_eq_B (by omega)
    · exact False.elim (ggWeylTypeB_ne_D hB.1 hD'.1 (by omega))
    · obtain ⟨rfl, rfl, -⟩ := hE6'
      have hEq : 2 ^ r * r.factorial = 51840 := by omega
      have hbound : r ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE7'
      have hEq : 2 ^ r * r.factorial = 2903040 := by omega
      have hbound : r ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE8'
      have hEq : 2 ^ r * r.factorial = 696729600 := by omega
      have hbound : r ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hF4'
      have hEq : 2 ^ r * r.factorial = 1152 := by omega
      have hbound : r ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hG2'
      have hEq : 2 ^ r * r.factorial = 12 := by omega
      have hbound : r ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · have hsr : s = r := ggWeylTypeA_rank_eq_D (r := s) (s := r) hD.1 (by omega)
      omega
    · exact False.elim (ggWeylTypeB_ne_D hB'.1 hD.1 (by omega))
    · exact ggWeylTypeD_rank_eq_D hD.1 hD'.1 (by omega)
    · obtain ⟨rfl, rfl, -⟩ := hE6'
      have hEq : 2 ^ (r - 1) * r.factorial = 51840 := by omega
      have hbound : r ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE7'
      have hEq : 2 ^ (r - 1) * r.factorial = 2903040 := by omega
      have hbound : r ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE8'
      have hEq : 2 ^ (r - 1) * r.factorial = 696729600 := by omega
      have hbound : r ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hF4'
      have hEq : 2 ^ (r - 1) * r.factorial = 1152 := by omega
      have hbound : r ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hG2'
      have hEq : 2 ^ (r - 1) * r.factorial = 12 := by omega
      have hbound : r ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases r <;> norm_num at hEq
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · obtain ⟨rfl, rfl, -⟩ := hE6
      have hEq : (s + 1).factorial = 51840 := by omega
      have hbound : s ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE6
      have hEq : 2 ^ s * s.factorial = 51840 := by omega
      have hbound : s ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE6
      have hEq : 2 ^ (s - 1) * s.factorial = 51840 := by omega
      have hbound : s ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE6
      obtain ⟨rfl, -, -⟩ := hE6'
      rfl
    · obtain ⟨rfl, hn, -⟩ := hE6
      obtain ⟨rfl, hn', -⟩ := hE7'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE6
      obtain ⟨rfl, hn', -⟩ := hE8'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE6
      obtain ⟨rfl, hn', -⟩ := hF4'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE6
      obtain ⟨rfl, hn', -⟩ := hG2'
      omega
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · obtain ⟨rfl, rfl, -⟩ := hE7
      have hEq : (s + 1).factorial = 2903040 := by omega
      have hbound : s ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE7
      have hEq : 2 ^ s * s.factorial = 2903040 := by omega
      have hbound : s ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE7
      have hEq : 2 ^ (s - 1) * s.factorial = 2903040 := by omega
      have hbound : s ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, hn, -⟩ := hE7
      obtain ⟨rfl, hn', -⟩ := hE6'
      omega
    · obtain ⟨rfl, rfl, -⟩ := hE7
      obtain ⟨rfl, -, -⟩ := hE7'
      rfl
    · obtain ⟨rfl, hn, -⟩ := hE7
      obtain ⟨rfl, hn', -⟩ := hE8'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE7
      obtain ⟨rfl, hn', -⟩ := hF4'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE7
      obtain ⟨rfl, hn', -⟩ := hG2'
      omega
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · obtain ⟨rfl, rfl, -⟩ := hE8
      have hEq : (s + 1).factorial = 696729600 := by omega
      have hbound : s ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE8
      have hEq : 2 ^ s * s.factorial = 696729600 := by omega
      have hbound : s ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hE8
      have hEq : 2 ^ (s - 1) * s.factorial = 696729600 := by omega
      have hbound : s ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, hn, -⟩ := hE8
      obtain ⟨rfl, hn', -⟩ := hE6'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE8
      obtain ⟨rfl, hn', -⟩ := hE7'
      omega
    · obtain ⟨rfl, rfl, -⟩ := hE8
      obtain ⟨rfl, -, -⟩ := hE8'
      rfl
    · obtain ⟨rfl, hn, -⟩ := hE8
      obtain ⟨rfl, hn', -⟩ := hF4'
      omega
    · obtain ⟨rfl, hn, -⟩ := hE8
      obtain ⟨rfl, hn', -⟩ := hG2'
      omega
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · obtain ⟨rfl, rfl, -⟩ := hF4
      have hEq : (s + 1).factorial = 1152 := by omega
      have hbound : s ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hF4
      have hEq : 2 ^ s * s.factorial = 1152 := by omega
      have hbound : s ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hF4
      have hEq : 2 ^ (s - 1) * s.factorial = 1152 := by omega
      have hbound : s ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, hn, -⟩ := hF4
      obtain ⟨rfl, hn', -⟩ := hE6'
      omega
    · obtain ⟨rfl, hn, -⟩ := hF4
      obtain ⟨rfl, hn', -⟩ := hE7'
      omega
    · obtain ⟨rfl, hn, -⟩ := hF4
      obtain ⟨rfl, hn', -⟩ := hE8'
      omega
    · obtain ⟨rfl, rfl, -⟩ := hF4
      obtain ⟨rfl, -, -⟩ := hF4'
      rfl
    · obtain ⟨rfl, hn, -⟩ := hF4
      obtain ⟨rfl, hn', -⟩ := hG2'
      omega
  ·
    rcases hs with hA' | hB' | hD' | hE6' | hE7' | hE8' | hF4' | hG2'
    · obtain ⟨rfl, rfl, -⟩ := hG2
      have hEq : (s + 1).factorial = 12 := by omega
      have hbound : s ≤ 11 := ggWeylTypeA_rank_le_of_factorial_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hG2
      have hEq : 2 ^ s * s.factorial = 12 := by omega
      have hbound : s ≤ 9 := ggWeylTypeB_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, rfl, -⟩ := hG2
      have hEq : 2 ^ (s - 1) * s.factorial = 12 := by omega
      have hbound : s ≤ 9 := ggWeylTypeD_rank_le_of_order_le hEq.le (by norm_num)
      interval_cases s <;> norm_num at hEq
    · obtain ⟨rfl, hn, -⟩ := hG2
      obtain ⟨rfl, hn', -⟩ := hE6'
      omega
    · obtain ⟨rfl, hn, -⟩ := hG2
      obtain ⟨rfl, hn', -⟩ := hE7'
      omega
    · obtain ⟨rfl, hn, -⟩ := hG2
      obtain ⟨rfl, hn', -⟩ := hE8'
      omega
    · obtain ⟨rfl, hn, -⟩ := hG2
      obtain ⟨rfl, hn', -⟩ := hF4'
      omega
    · obtain ⟨rfl, rfl, -⟩ := hG2
      obtain ⟨rfl, -, -⟩ := hG2'
      rfl

theorem ggWeylTypeData_rank_eq_of_mulEquiv
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {M : CoxeterMatrix ι} {N : CoxeterMatrix κ}
    (hM : GGIsWeylMatrix M) (hN : GGIsWeylMatrix N) (e : M.Group ≃* N.Group) :
    Fintype.card ι = Fintype.card κ := by
  have hMdata := ggWeylTypeData_of_isWeylMatrix hM
  have hNdata := ggWeylTypeData_of_isWeylMatrix hN
  have hcard : Nat.card M.Group = Nat.card N.Group := Nat.card_congr e.toEquiv
  have hNdata' : GGWeylTypeData (Fintype.card κ) (Nat.card M.Group)
      (Nat.card ↥(Subgroup.center N.Group)) := by
    simpa only [hcard] using hNdata
  exact ggWeylTypeData_rank_eq hMdata hNdata'

theorem ggWeylTypeData_card_le_twelve_of_rank_le_two {r n c : ℕ}
    (h : GGWeylTypeData r n c) (hr : r ≤ 2) : n ≤ 12 := by
  rcases h with hA | hB | hD | hE6 | hE7 | hE8 | hF4 | hG2
  · have hfac := Nat.factorial_le (show r + 1 ≤ 3 by omega)
    norm_num at hfac
    omega
  · have hr2 : r = 2 := by omega
    subst r
    norm_num at hB
    omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

end CFSG.StandardType

end
