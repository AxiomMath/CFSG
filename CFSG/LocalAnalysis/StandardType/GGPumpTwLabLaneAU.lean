module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabDefs
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabRigid
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabCompNe
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALinearBranch
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAUnitaryBranch
import CFSG.LocalAnalysis.StandardType.GGK1ScMain
import CFSG.LocalAnalysis.StandardType.GGMultTableCl
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNTUnivHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem l04fHL2_two_pow_two_mul_sub_one (n : ℕ) :
    2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  have h : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [show 2 * n = n * 2 by omega, pow_mul]
  rw [h]
  nth_rewrite 1 [show (1 : ℕ) = 1 ^ 2 by norm_num]
  rw [Nat.sq_sub_sq]
  ring

private theorem l04fHL2_absurd_sub_add {a : ℕ} (h1 : 3 ∣ 2 ^ a - 1) (h2 : 3 ∣ 2 ^ a + 1) : False := by
  have h2' : 3 ∣ 2 ^ a + 1 - (2 ^ a - 1) := Nat.dvd_sub h2 h1
  have hsub : 2 ^ a + 1 - (2 ^ a - 1) = 2 := by
    have hpow : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    omega
  rw [hsub] at h2'
  norm_num at h2'

private theorem l04fHL2_absurd_sq_add_of_sub {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    ¬ 3 ∣ 2 ^ (2 * n) + 1 := by
  intro h2
  have h1 : 3 ∣ 2 ^ (2 * n) - 1 := by
    rw [l04fHL2_two_pow_two_mul_sub_one]
    exact dvd_mul_of_dvd_left h _
  exact l04fHL2_absurd_sub_add h1 h2

private theorem l04fHL2_absurd_sq_add_of_add {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    ¬ 3 ∣ 2 ^ (2 * n) + 1 := by
  intro h2
  have h1 : 3 ∣ 2 ^ (2 * n) - 1 := by
    rw [l04fHL2_two_pow_two_mul_sub_one]
    exact dvd_mul_of_dvd_right h _
  exact l04fHL2_absurd_sub_add h1 h2

private theorem l04fHL2_sum_eq_finset (m : List ℕ) :
    m.sum = ∑ j ∈ Finset.range m.length, m.getD j 0 := by
  induction m with
  | nil => simp
  | cons x xs ih =>
      rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega

private theorem l04fHL2_ord_eq_one {n : ℕ} (h : ggMultOrd 3 n = 1) : 3 ∣ 2 ^ n - 1 := by
  unfold ggMultOrd at h
  by_cases h1 : 3 ∣ 2 ^ n - 1
  · exact h1
  · rw [if_neg h1] at h
    split_ifs at h
    omega

private theorem l04fHL2_ord_eq_two {n : ℕ} (h : ggMultOrd 3 n = 2) : 3 ∣ 2 ^ n + 1 := by
  unfold ggMultOrd at h
  by_cases h1 : 3 ∣ 2 ^ n - 1
  · rw [if_pos h1] at h; omega
  · rw [if_neg h1] at h
    by_cases h2 : 3 ∣ 2 ^ n + 1
    · exact h2
    · rw [if_neg h2] at h; omega

private theorem l04fHL2_ord_eq_one_or_two {n : ℕ} (hd : ggMultOrd 3 n ≠ 0) :
    ggMultOrd 3 n = 1 ∨ ggMultOrd 3 n = 2 := by
  by_cases h1 : 3 ∣ 2 ^ n - 1
  · unfold ggMultOrd; rw [if_pos h1]; exact Or.inl rfl
  · by_cases h2 : 3 ∣ 2 ^ n + 1
    · unfold ggMultOrd; rw [if_neg h1, if_pos h2]; exact Or.inr rfl
    · exfalso; unfold ggMultOrd at hd; rw [if_neg h1, if_neg h2] at hd; exact hd rfl

private theorem l04fHL2_ggMultOrd_ne_zero {n : ℕ}
    (h : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) : ggMultOrd 3 n ≠ 0 := by
  unfold ggMultOrd
  by_cases h1 : 3 ∣ 2 ^ n - 1
  · rw [if_pos h1]; norm_num
  · rw [if_neg h1]
    have h2 : 3 ∣ 2 ^ n + 1 := by
      rcases h with h | h
      · exact absurd h h1
      · exact h
    rw [if_pos h2]; norm_num

private theorem l04fHL2_sum_three {m : List ℕ} (hlen : m.length = 3) :
    m.sum = m.getD 0 0 + m.getD 1 0 + m.getD 2 0 := by
  rw [l04fHL2_sum_eq_finset m, hlen]
  norm_num [Finset.sum_range_succ]

private theorem l04fHL2_sum_symm_three {m : List ℕ} (hlen : m.length = 3)
    (hsymm : ∀ j, j < 3 → m.getD ((3 - j) % 3) 0 = m.getD j 0) :
    m.sum = m.headD 0 + 2 * m.getD 1 0 := by
  have h2 := hsymm 2 (by norm_num)
  have h20 : m.getD ((3 - 2) % 3) 0 = m.getD 2 0 := h2
  simp only [show (3 - 2) % 3 = 1 by norm_num] at h20
  rw [l04fHL2_sum_three hlen, ← List.headD_eq_getD, ← h20]
  ring

private theorem l04fHL2_blockA_two {r n : ℕ} (hr : 2 ≤ r) :
    (ggMultBlockA r n 2).lab = (⟨.twA, r, n⟩ : LargeEvenLabel) := by
  simp [ggMultBlockA, hr]

private theorem l04fHL2_blockA_two_small {r n : ℕ} (hr : ¬ 2 ≤ r) :
    (ggMultBlockA r n 2).lab = (⟨.A, 1, n⟩ : LargeEvenLabel) := by
  simp [ggMultBlockA, hr]

private theorem l04fHL2_orbit_tagA
    {r n : ℕ} (hF : GGKacGenericClA (⟨.A, r, n⟩ : LargeEvenLabel) 3)
    {D : GGKacDatum} (hvalid : GGMultValidCl (⟨.A, r, n⟩ : LargeEvenLabel) 3 D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) {f : ℕ}
    (hrig : (o.lab = (⟨.A, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f + 1) ∨
            (o.lab = (⟨.twA, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f - 1) ∨
            o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel))
    (hne : o.lab ≠ (⟨.A, r, n⟩ : LargeEvenLabel)) :
    GGPumpTwLabConcl (⟨.A, r, n⟩ : LargeEvenLabel) f := by
  obtain ⟨T, tw, nf, hT, hDmem⟩ := hvalid
  simp only [ggKacTypeClOfLabel, Option.some.injEq, Prod.mk.injEq] at hT
  obtain ⟨rfl, rfl, rfl⟩ := hT
  have hdiv : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := hF.1.2.2.1
  have hd : ggMultOrd 3 n ≠ 0 := l04fHL2_ggMultOrd_ne_zero hdiv
  obtain ⟨m, hmlen, hmsum, hadm, hDeq⟩ := (mem_ggMultTableCl_A hd).mp hDmem
  rw [hDeq] at ho
  rcases l04fHL2_ord_eq_one_or_two hd with hd1 | hd2
  · rw [hd1] at ho
    simp only [ggMultDatumA] at ho
    rw [if_pos (by decide)] at ho
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
    obtain ⟨j, ⟨hj, hmj⟩, hjo⟩ := ho
    have hlabo : o.lab = (⟨.A, m.getD j 0 - 1, n⟩ : LargeEvenLabel) := by
      rw [← hjo]; simp [ggMultBlockA]
    rcases hrig with hA5 | htwA5 | htwD
    · have heq : (⟨.A, m.getD j 0 - 1, n⟩ : LargeEvenLabel) = ⟨.A, 5, f⟩ := by
        rw [← hlabo]; exact hA5.1
      have hnf : n = f := by have := congrArg LargeEvenLabel.n heq; simpa using this
      rw [← hnf] at hA5
      exact absurd hA5.2 (l04fHL2_absurd_sub_add (l04fHL2_ord_eq_one hd1))
    · rw [hlabo] at htwA5
      exact absurd htwA5.1 (by simp)
    · rw [hlabo] at htwD
      exact absurd htwD (by simp)
  · rw [hd2] at ho
    simp only [ggMultDatumA] at ho
    rw [if_neg (by decide)] at ho
    have hsymm : ∀ j, j < 3 → m.getD ((3 - j) % 3) 0 = m.getD j 0 := by
      rcases hadm with ⟨-, h1⟩ | ⟨h2, -⟩ | hsymm
      · rw [hd2] at h1; exact absurd h1 (by decide)
      · exact absurd h2 (by decide)
      · exact hsymm
    simp only [if_true, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at ho
    rcases ho with ho0 | ⟨j, ⟨hj2, hj1, hmj⟩, hjo⟩
    · by_cases h0 : 2 ≤ m.headD 0
      · simp only [if_pos h0, List.mem_singleton] at ho0
        have hlabo : o.lab = (⟨.A, m.headD 0 - 1, n⟩ : LargeEvenLabel) := by rw [ho0]
        rcases hrig with hA5 | htwA5 | htwD
        · have heq : (⟨.A, m.headD 0 - 1, n⟩ : LargeEvenLabel) = ⟨.A, 5, f⟩ := by
            rw [← hlabo]; exact hA5.1
          have hnf : n = f := by have := congrArg LargeEvenLabel.n heq; simpa using this
          have hm0 : m.headD 0 = 6 := by
            have hrr : m.headD 0 - 1 = 5 := congrArg LargeEvenLabel.rank heq
            omega
          have hsum : m.sum = m.headD 0 + 2 * m.getD 1 0 := l04fHL2_sum_symm_three hmlen hsymm
          have hrmain : r = 5 + 2 * m.getD 1 0 := by
            have h : m.sum = r + 1 := hmsum
            rw [hsum, hm0] at h; omega
          have hk1 : 1 ≤ m.getD 1 0 := by
            by_contra hk
            have hk0 : m.getD 1 0 = 0 := by omega
            apply hne
            rw [hlabo, hm0, hrmain, hk0]
          exact ⟨hnf, Or.inl ⟨m.getD 1 0, hk1, Or.inl ⟨by rw [hrmain, hnf], hA5.2⟩⟩⟩
        · rw [hlabo] at htwA5
          exact absurd htwA5.1 (by simp)
        · rw [hlabo] at htwD
          exact absurd htwD (by simp)
      · simp only [if_neg h0] at ho0
        exact absurd ho0 (by simp)
    · have hlabo : o.lab = (⟨.A, m.getD j 0 - 1, 2 * n⟩ : LargeEvenLabel) := by rw [← hjo]
      rcases hrig with hA5 | htwA5 | htwD
      · have heq : (⟨.A, m.getD j 0 - 1, 2 * n⟩ : LargeEvenLabel) = ⟨.A, 5, f⟩ := by
          rw [← hlabo]; exact hA5.1
        have hnf : 2 * n = f := by have := congrArg LargeEvenLabel.n heq; simpa using this
        rw [← hnf] at hA5
        exact absurd hA5.2 (l04fHL2_absurd_sq_add_of_add (l04fHL2_ord_eq_two hd2))
      · rw [hlabo] at htwA5
        exact absurd htwA5.1 (by simp)
      · rw [hlabo] at htwD
        exact absurd htwD (by simp)


private theorem l04fHL2_orbit_tagtwA
    {r n : ℕ} (hF : GGKacGenericClA (⟨.twA, r, n⟩ : LargeEvenLabel) 3)
    {D : GGKacDatum} (hvalid : GGMultValidCl (⟨.twA, r, n⟩ : LargeEvenLabel) 3 D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) {f : ℕ}
    (hrig : (o.lab = (⟨.A, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f + 1) ∨
            (o.lab = (⟨.twA, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f - 1) ∨
            o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel))
    (hne : o.lab ≠ (⟨.twA, r, n⟩ : LargeEvenLabel)) :
    GGPumpTwLabConcl (⟨.twA, r, n⟩ : LargeEvenLabel) f := by
  obtain ⟨T, tw, nf, hT, hDmem⟩ := hvalid
  simp only [ggKacTypeClOfLabel, Option.some.injEq, Prod.mk.injEq] at hT
  obtain ⟨rfl, rfl, rfl⟩ := hT
  have hdiv : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := hF.1.2.2.1
  have hd : ggMultOrd 3 n ≠ 0 := l04fHL2_ggMultOrd_ne_zero hdiv
  obtain ⟨m, hmlen, hmsum, hadm, hDeq⟩ := (mem_ggMultTableCl_A hd).mp hDmem
  rw [hDeq] at ho
  rcases l04fHL2_ord_eq_one_or_two hd with hd1 | hd2
  · rw [hd1] at ho
    simp only [ggMultDatumA] at ho
    rw [if_neg (by decide)] at ho
    have hsymm : ∀ j, j < 3 → m.getD ((3 - j) % 3) 0 = m.getD j 0 := by
      rcases hadm with ⟨h1, -⟩ | ⟨-, h2⟩ | hsymm
      · exact absurd h1 (by decide)
      · rw [hd1] at h2; exact absurd h2 (by decide)
      · exact hsymm
    simp only [Bool.true_eq_false, if_false, List.mem_append, List.mem_map, List.mem_filter,
      List.mem_range, decide_eq_true_eq] at ho
    rcases ho with ho0 | ⟨j, ⟨hj2, hj1, hmj⟩, hjo⟩
    · by_cases h0 : 2 ≤ m.headD 0
      · simp only [if_pos h0, List.mem_singleton] at ho0
        have hlabo : o.lab = (ggMultBlockA (m.headD 0 - 1) n 2).lab := by rw [ho0]
        by_cases hr2 : 2 ≤ m.headD 0 - 1
        · have hlab : o.lab = (⟨.twA, m.headD 0 - 1, n⟩ : LargeEvenLabel) := by
            rw [hlabo, l04fHL2_blockA_two hr2]
          rcases hrig with hA5 | htwA5 | htwD
          · rw [hlab] at hA5; exact absurd hA5.1 (by simp)
          · have heq : (⟨.twA, m.headD 0 - 1, n⟩ : LargeEvenLabel) = ⟨.twA, 5, f⟩ := by
              rw [← hlab]; exact htwA5.1
            have hnf : n = f := by have := congrArg LargeEvenLabel.n heq; simpa using this
            have hm0 : m.headD 0 = 6 := by
              have hrr : m.headD 0 - 1 = 5 := congrArg LargeEvenLabel.rank heq
              omega
            have hsum : m.sum = m.headD 0 + 2 * m.getD 1 0 := l04fHL2_sum_symm_three hmlen hsymm
            have hrmain : r = 5 + 2 * m.getD 1 0 := by
              have h : m.sum = r + 1 := hmsum
              rw [hsum, hm0] at h; omega
            have hk1 : 1 ≤ m.getD 1 0 := by
              by_contra hk
              have hk0 : m.getD 1 0 = 0 := by omega
              apply hne
              rw [hlab, hm0, hrmain, hk0]
            exact ⟨hnf, Or.inl ⟨m.getD 1 0, hk1, Or.inr (Or.inl ⟨by rw [hrmain, hnf], htwA5.2⟩)⟩⟩
          · rw [hlab] at htwD; exact absurd htwD (by simp)
        · have hlab : o.lab = (⟨.A, 1, n⟩ : LargeEvenLabel) := by
            rw [hlabo, l04fHL2_blockA_two_small hr2]
          rcases hrig with hA5 | htwA5 | htwD
          · rw [hlab] at hA5; exact absurd hA5.1 (by simp)
          · rw [hlab] at htwA5; exact absurd htwA5.1 (by simp)
          · rw [hlab] at htwD; exact absurd htwD (by simp)
      · simp only [if_neg h0] at ho0
        exact absurd ho0 (by simp)
    · have hlabo : o.lab = (⟨.A, m.getD j 0 - 1, 2 * n⟩ : LargeEvenLabel) := by rw [← hjo]
      rcases hrig with hA5 | htwA5 | htwD
      · have heq : (⟨.A, m.getD j 0 - 1, 2 * n⟩ : LargeEvenLabel) = ⟨.A, 5, f⟩ := by
          rw [← hlabo]; exact hA5.1
        have hnf : 2 * n = f := by have := congrArg LargeEvenLabel.n heq; simpa using this
        rw [← hnf] at hA5
        exact absurd hA5.2 (l04fHL2_absurd_sq_add_of_sub (l04fHL2_ord_eq_one hd1))
      · rw [hlabo] at htwA5; exact absurd htwA5.1 (by simp)
      · rw [hlabo] at htwD; exact absurd htwD (by simp)
  · rw [hd2] at ho
    simp only [ggMultDatumA] at ho
    rw [if_pos (by decide)] at ho
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
    obtain ⟨j, ⟨hj, hmj⟩, hjo⟩ := ho
    have hlabo : o.lab = (ggMultBlockA (m.getD j 0 - 1) n 2).lab := by rw [hjo]
    by_cases hr2 : 2 ≤ m.getD j 0 - 1
    · have hlab : o.lab = (⟨.twA, m.getD j 0 - 1, n⟩ : LargeEvenLabel) := by
        rw [hlabo, l04fHL2_blockA_two hr2]
      rcases hrig with hA5 | htwA5 | htwD
      · rw [hlab] at hA5; exact absurd hA5.1 (by simp)
      · have heq : (⟨.twA, m.getD j 0 - 1, n⟩ : LargeEvenLabel) = ⟨.twA, 5, f⟩ := by
          rw [← hlab]; exact htwA5.1
        have hnf : n = f := by have := congrArg LargeEvenLabel.n heq; simpa using this
        rw [← hnf] at htwA5
        exact absurd (l04fHL2_ord_eq_two hd2) (l04fHL2_absurd_sub_add htwA5.2)
      · rw [hlab] at htwD; exact absurd htwD (by simp)
    · have hlab : o.lab = (⟨.A, 1, n⟩ : LargeEvenLabel) := by
        rw [hlabo, l04fHL2_blockA_two_small hr2]
      rcases hrig with hA5 | htwA5 | htwD
      · rw [hlab] at hA5; exact absurd hA5.1 (by simp)
      · rw [hlab] at htwA5; exact absurd htwA5.1 (by simp)
      · rw [hlab] at htwD; exact absurd htwD (by simp)


private theorem l04fHL2_getD_mem {m : List ℕ} {j : ℕ} (hj : j < m.length) : m.getD j 0 ∈ m := by
  induction m generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.getD_cons_succ]
          exact List.mem_cons_of_mem _ (ih (by simpa using hj))

private theorem l04fHL2_headD_mem {m : List ℕ} (hlen : 0 < m.length) : m.headD 0 ∈ m := by
  rw [List.headD_eq_getD]
  exact l04fHL2_getD_mem (j := 0) hlen

private theorem l04fHL2_dvd_sq_sub_one_of_sub {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    3 ∣ 2 ^ (2 * n) - 1 := by
  rw [l04fHL2_two_pow_two_mul_sub_one]
  exact dvd_mul_of_dvd_left h _

private theorem l04fHL2_dvd_sq_sub_one_of_add {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    3 ∣ 2 ^ (2 * n) - 1 := by
  rw [l04fHL2_two_pow_two_mul_sub_one]
  exact dvd_mul_of_dvd_right h _

private theorem l04fHL2_ggMultOrd_two_mul_ne_zero {n : ℕ}
    (h : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) : ggMultOrd 3 (2 * n) ≠ 0 := by
  apply l04fHL2_ggMultOrd_ne_zero
  rcases h with h | h
  · exact Or.inl (l04fHL2_dvd_sq_sub_one_of_sub h)
  · exact Or.inl (l04fHL2_dvd_sq_sub_one_of_add h)

private theorem l04fHL2_le_sum_of_mem {m : List ℕ} {x : ℕ} (hx : x ∈ m) : x ≤ m.sum := by
  induction m with
  | nil => simp at hx
  | cons y ys ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := ih hx; omega

private theorem l04fHL2_blockA_rank_le {r n d B : ℕ} (hr : r ≤ B) (hB1 : 1 ≤ B) :
    (ggMultBlockA r n d).lab.rank ≤ B := by
  unfold ggMultBlockA
  split_ifs <;> simp_all

private theorem l04fHL2_datumA_orbit_rank_le {n d B : ℕ} {tw : Bool} {m : List ℕ} {o : GGKacOrbit}
    (hlen : m.length = 3) (hB : ∀ x ∈ m, x ≤ B + 1) (hB1 : 1 ≤ B)
    (ho : o ∈ (ggMultDatumA 3 n d tw m).orbits) : o.lab.rank ≤ B := by
  by_cases htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  · simp only [ggMultDatumA] at ho
    rw [if_pos htriv] at ho
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
    obtain ⟨j, ⟨hj, hmj⟩, hjo⟩ := ho
    have hmem : m.getD j 0 ∈ m := l04fHL2_getD_mem (by omega)
    have hle : m.getD j 0 - 1 ≤ B := by have := hB _ hmem; omega
    rw [← hjo]
    exact l04fHL2_blockA_rank_le hle hB1
  · simp only [ggMultDatumA] at ho
    rw [if_neg htriv] at ho
    simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at ho
    rcases ho with ho0 | ⟨j, ⟨hj, hmj⟩, hjo⟩
    · by_cases h0 : 2 ≤ m.headD 0
      · simp only [if_pos h0] at ho0
        by_cases htw : tw = false
        · simp only [if_pos htw, List.mem_singleton] at ho0
          have hmem : m.headD 0 ∈ m := l04fHL2_headD_mem (by omega)
          have hle : m.headD 0 - 1 ≤ B := by have := hB _ hmem; omega
          rw [ho0]
          exact hle
        · simp only [if_neg htw, List.mem_singleton] at ho0
          have hmem : m.headD 0 ∈ m := l04fHL2_headD_mem (by omega)
          have hle : m.headD 0 - 1 ≤ B := by have := hB _ hmem; omega
          rw [ho0]
          exact l04fHL2_blockA_rank_le hle hB1
      · simp only [if_neg h0] at ho0
        exact absurd ho0 (by simp)
    · have hmem : m.getD j 0 ∈ m := l04fHL2_getD_mem (by omega)
      have hle : m.getD j 0 - 1 ≤ B := by have := hB _ hmem; omega
      rw [← hjo]
      exact hle

private theorem l04fHL2_orbit_small_false
    {rr nf : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit} {f : ℕ}
    (hord : ggMultOrd 3 nf ≠ 0)
    (hDmem : D ∈ ggMultTableCl (.A rr) tw 3 nf)
    (ho : o ∈ D.orbits)
    (hrig : (o.lab = (⟨.A, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f + 1) ∨
            (o.lab = (⟨.twA, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f - 1) ∨
            o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel))
    (hrr1 : 1 ≤ rr) (hrr : rr ≤ 3) : False := by
  obtain ⟨m, hmlen, hmsum, hadm, hDeq⟩ := (mem_ggMultTableCl_A hord).mp hDmem
  rw [hDeq] at ho
  have hbound : ∀ x ∈ m, x ≤ rr + 1 := by
    intro x hx
    have hx' := l04fHL2_le_sum_of_mem hx
    rw [hmsum] at hx'
    exact hx'
  have hrank := l04fHL2_datumA_orbit_rank_le hmlen hbound hrr1 ho
  rcases hrig with ⟨h1, -⟩ | ⟨h2, -⟩ | h3
  · rw [h1] at hrank; simp at hrank; omega
  · rw [h2] at hrank; simp at hrank; omega
  · rw [h3] at hrank; simp at hrank; omega

private theorem l04fHL2_orbit_A
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hF : GGKacGenericClA lab 3)
    {D : GGKacDatum} (hvalid : GGMultValidCl lab 3 D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) {f : ℕ}
    (hrig : (o.lab = (⟨.A, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f + 1) ∨
            (o.lab = (⟨.twA, 5, f⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ f - 1) ∨
            o.lab = (⟨.twD, 4, f⟩ : LargeEvenLabel))
    (hne : o.lab ≠ lab) : GGPumpTwLabConcl lab f := by
  rcases lab with ⟨tag, r, n⟩
  rcases hF.2 with hA | htwA | ⟨hD, hr3⟩ | ⟨htwD, hrle⟩
  · subst hA
    exact l04fHL2_orbit_tagA hF hvalid ho hrig hne
  · subst htwA
    exact l04fHL2_orbit_tagtwA hF hvalid ho hrig hne
  · subst hD; subst hr3
    obtain ⟨T, tw, nf, hT, hDmem⟩ := hvalid
    simp only [ggKacTypeClOfLabel] at hT
    obtain ⟨rfl, rfl, rfl⟩ := hT
    exact (l04fHL2_orbit_small_false (l04fHL2_ggMultOrd_ne_zero hF.1.2.2.1) hDmem ho hrig
      (by omega) (by omega)).elim
  · subst htwD
    simp only [LargeEvenInLambda2] at hlab
    have hr2 : 2 ≤ r := hlab.2
    have hrle' : r ≤ 3 := hrle
    obtain ⟨T, tw, nf, hT, hDmem⟩ := hvalid
    rcases (show r = 2 ∨ r = 3 by omega) with rfl | rfl
    · simp only [ggKacTypeClOfLabel] at hT
      obtain ⟨rfl, rfl, rfl⟩ := hT
      exact (l04fHL2_orbit_small_false (l04fHL2_ggMultOrd_two_mul_ne_zero hF.1.2.2.1) hDmem ho
        hrig (by omega) (by omega)).elim
    · simp only [ggKacTypeClOfLabel] at hT
      obtain ⟨rfl, rfl, rfl⟩ := hT
      exact (l04fHL2_orbit_small_false (l04fHL2_ggMultOrd_ne_zero hF.1.2.2.1) hDmem ho hrig
        (by omega) (by omega)).elim

theorem ggPumpTwLab_laneAU
    (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab) (hF : GGKacGenericClA lab 3) :
    GGPumpTwLabAt lab := by
  refine LargeEvenLabelAll.mono ?_ (largeEvenLabelAll_and (ggK0Main_cl 3 lab hlab hF.1)
    (largeEvenLabelAll_hasLabel lab))
  intro R _ I F hP L' _ _ ψ hψ hker hperf e J f he1 he3 hφ hJ hJlab
  obtain ⟨D, hvalid, ha, -⟩ := hP.1 L' ψ hψ hker hperf e he3 hφ
  obtain ⟨o, ho, _, _, hoΛ, hohas⟩ := ha J hJ
  refine l04fHL2_orbit_A hlab hF hvalid ho ?_ ?_
  · exact ggPumpTwJLab_rigid hJlab hoΛ hohas
  · intro h
    exact ggPumpTw_component_label_ne ψ hψ hker hperf hP.2 he1 hJ (h ▸ hohas)

theorem ggPumpTwLabAt_linear_of_three_dvd_sub_one
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .A)
    (h3 : 3 ∣ 2 ^ lab.n - 1) : GGPumpTwLabAt lab := by
  apply ggPumpTwLabAt_of_component_exclusion hlab
  intro R _ _ hcen φ hin hφ3 Jb hJb f hJlab
  obtain ⟨labC, hΛC, htagC, hdeg, hC⟩ :=
    GGInnerD4RAParts.exists_linear_component_label hcen hlab htag hφ3 hin hJb
  have hsub : 3 ∣ 2 ^ labC.n - 1 :=
    h3.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hdeg)
  rcases ggPumpTwJLab_rigid hJlab hΛC hC with ⟨hA, hplus⟩ | ⟨hU, -⟩ | hD
  · have hsubf : 3 ∣ 2 ^ f - 1 := by simpa only [hA] using hsub
    exact (l04fHL2_absurd_sub_add hsubf hplus).elim
  · rw [hU] at htagC
    cases htagC
  · rw [hD] at htagC
    cases htagC

theorem ggPumpTwLabAt_unitary_of_three_dvd_add_one
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twA)
    (h3 : 3 ∣ 2 ^ lab.n + 1) : GGPumpTwLabAt lab := by
  apply ggPumpTwLabAt_of_component_exclusion hlab
  intro R _ _ hcen φ hin hφ3 Jb hJb f hJlab
  obtain ⟨dd, labC, hdd, hdeg, hΛC, htagC, hC⟩ :=
    GGInnerD4RAParts.exists_unitary_component_label_of_dvd_add_one
      Nat.prime_three (by decide) hcen htag hφ3 h3 hin hJb
  have hodd : Odd dd := (by decide : Odd (3 : ℕ)).of_dvd_nat hdd
  have hplus : 3 ∣ 2 ^ labC.n + 1 := by
    rw [hdeg, pow_mul]
    exact h3.trans (by simpa using
      (hodd.nat_add_dvd_pow_add_pow (x := 2 ^ lab.n) (y := 1)))
  rcases ggPumpTwJLab_rigid hJlab hΛC hC with ⟨hA, -⟩ | ⟨hU, hsub⟩ | hD
  · rcases htagC with ⟨-, hr⟩ | ht
    · rw [hA] at hr
      norm_num at hr
    · rw [hA] at ht
      cases ht
  · have hplusf : 3 ∣ 2 ^ f + 1 := by simpa only [hU] using hplus
    exact (l04fHL2_absurd_sub_add hsub hplusf).elim
  · rcases htagC with ⟨ht, -⟩ | ht
    · rw [hD] at ht
      cases ht
    · rw [hD] at ht
      cases ht

theorem ggPumpTwLabRAKnown_holds
    : GGPumpTwLabRAKnown := by
  intro lab hlab hRA
  rcases hRA with ⟨hA, -, hsub⟩ | ⟨hU, -, hplus⟩
  · exact ggPumpTwLabAt_linear_of_three_dvd_sub_one hlab hA hsub
  · exact ggPumpTwLabAt_unitary_of_three_dvd_add_one hlab hU hplus

end CFSG.StandardType

end
