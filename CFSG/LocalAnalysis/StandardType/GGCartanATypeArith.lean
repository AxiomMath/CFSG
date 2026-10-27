module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.StandardType

@[expose] def ggCartanAMod (n p : ℕ) (i j : Fin n) : ZMod p :=
  ((CartanMatrix.A n i j : ℤ) : ZMod p)

@[expose] def ggCartanARad (n p : ℕ) (i : Fin n) : ZMod p := (((i : ℕ) + 1 : ℕ) : ZMod p)

theorem ggCartanAMod_apply (n p : ℕ) (i j : Fin n) :
    ggCartanAMod n p i j =
      if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 := by
  simp only [ggCartanAMod, CartanMatrix.A, Matrix.of_apply]
  push_cast
  split_ifs <;> ring

private lemma ta_sum_eq_val {m p : ℕ} (f : Fin m → ZMod p) (a : ℕ) :
    (∑ k : Fin m, (if (k : ℕ) = a then f k else 0)) =
      if h : a < m then f ⟨a, h⟩ else 0 := by
  by_cases h : a < m
  · rw [dif_pos h]
    rw [Finset.sum_eq_single (⟨a, h⟩ : Fin m)
      (by intro b _ hb; exact if_neg (fun hba => hb (Fin.ext hba)))
      (by intro hmem; exact absurd (Finset.mem_univ _) hmem)]
    simp
  · rw [dif_neg h]
    exact Finset.sum_eq_zero (fun b _ => if_neg (fun hba => h (by omega)))

private lemma ta_sum_eq_pred {m p : ℕ} (f : Fin m → ZMod p) (a : ℕ) :
    (∑ k : Fin m, (if (k : ℕ) + 1 = a then f k else 0)) =
      if _h : 1 ≤ a then (if h2 : a - 1 < m then f ⟨a - 1, h2⟩ else 0) else 0 := by
  by_cases h : 1 ≤ a
  · rw [dif_pos h]
    by_cases h2 : a - 1 < m
    · rw [dif_pos h2]
      rw [Finset.sum_eq_single (⟨a - 1, h2⟩ : Fin m)
        (by
          intro b _ hb
          exact if_neg (fun hba => hb (Fin.ext (by omega : (b : ℕ) = a - 1))))
        (by intro hmem; exact absurd (Finset.mem_univ _) hmem)]
      rw [Nat.sub_add_cancel h, if_pos rfl]
    · rw [dif_neg h2]
      exact Finset.sum_eq_zero (fun k _ => if_neg (fun hk => by omega))
  · rw [dif_neg h]
    exact Finset.sum_eq_zero (fun k _ => if_neg (fun hk => by omega))

private lemma ta_sum_eq_succ {m p : ℕ} (f : Fin m → ZMod p) (a : ℕ) :
    (∑ k : Fin m, (if a + 1 = (k : ℕ) then f k else 0)) =
      if h : a + 1 < m then f ⟨a + 1, h⟩ else 0 := by
  by_cases h : a + 1 < m
  · rw [dif_pos h]
    rw [Finset.sum_eq_single (⟨a + 1, h⟩ : Fin m)
      (by intro b _ hb; exact if_neg (fun hba => hb (Fin.ext hba.symm)))
      (by intro hmem; exact absurd (Finset.mem_univ _) hmem)]
    simp
  · rw [dif_neg h]
    exact Finset.sum_eq_zero (fun b _ => if_neg (fun hba => by omega))

private lemma ta_sum_eq_fin {m p : ℕ} (f : Fin m → ZMod p) (a : Fin m) :
    (∑ k : Fin m, (if a = k then f k else 0)) = f a := by
  rw [Finset.sum_ite_eq]
  simp

private lemma ta_row_decomp_mul (n p : ℕ) (i : Fin n) (f : Fin n → ZMod p) (j : Fin n) :
    ggCartanAMod n p i j * f j
      = (if i = j then 2 * f j else 0)
        + (if (i : ℕ) + 1 = (j : ℕ) then -(f j) else 0)
        + (if (j : ℕ) + 1 = (i : ℕ) then -(f j) else 0) := by
  rw [ggCartanAMod_apply]
  by_cases h1 : i = j
  · have hv : (i : ℕ) = (j : ℕ) := congrArg Fin.val h1
    have h2 : ¬ (i : ℕ) + 1 = (j : ℕ) := by omega
    have h3 : ¬ (j : ℕ) + 1 = (i : ℕ) := by omega
    rw [if_pos h1, if_pos h1, if_neg h2, if_neg h3]; ring
  · by_cases h2 : (i : ℕ) + 1 = (j : ℕ)
    · have h3 : ¬ (j : ℕ) + 1 = (i : ℕ) := by omega
      rw [if_neg h1, if_pos (Or.inl h2), if_neg h1, if_pos h2, if_neg h3]; ring
    · by_cases h3 : (j : ℕ) + 1 = (i : ℕ)
      · rw [if_neg h1, if_pos (Or.inr h3), if_neg h1, if_neg h2, if_pos h3]; ring
      · rw [if_neg h1, if_neg (not_or.mpr ⟨h2, h3⟩), if_neg h1, if_neg h2, if_neg h3]; ring

private lemma ta_row_sum (n p : ℕ) (i : Fin n) (f : Fin n → ZMod p) :
    (∑ j : Fin n, ggCartanAMod n p i j * f j) =
      2 * f i
      + (if h : (i : ℕ) + 1 < n then -(f ⟨(i : ℕ) + 1, h⟩) else 0)
      + (if _h : 1 ≤ (i : ℕ) then
           (if h2 : (i : ℕ) - 1 < n then -(f ⟨(i : ℕ) - 1, h2⟩) else 0)
         else 0) := by
  rw [Finset.sum_congr rfl (fun j _ => ta_row_decomp_mul n p i f j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [ta_sum_eq_fin (fun j => 2 * f j) i]
  rw [ta_sum_eq_succ (fun j => -(f j)) (i : ℕ)]
  rw [ta_sum_eq_pred (fun j => -(f j)) (i : ℕ)]

private lemma ta_rad_eq (n p : ℕ) (j : Fin n) :
    ggCartanARad n p j = ((j : ℕ) : ZMod p) + 1 := by
  rw [ggCartanARad]
  push_cast
  ring

private lemma ta_rad_succ_val (n p : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    ggCartanARad n p ⟨(i : ℕ) + 1, h⟩ = (((i : ℕ) + 2 : ℕ) : ZMod p) := rfl

private lemma ta_rad_pred_val (n p : ℕ) (i : Fin n) (h : 1 ≤ (i : ℕ))
    (h2 : (i : ℕ) - 1 < n) :
    ggCartanARad n p ⟨(i : ℕ) - 1, h2⟩ = ((i : ℕ) : ZMod p) := by
  rw [ggCartanARad]
  rw [Nat.sub_add_cancel h]

theorem ggCartanAMod_rad (n p : ℕ) (hp : p ∣ n + 1) (i : Fin n) :
    ∑ j, ggCartanAMod n p i j * ggCartanARad n p j = 0 := by
  rw [ta_row_sum]
  by_cases h0 : (i : ℕ) = 0
  · rw [ta_rad_eq]
    have hpred : ¬ 1 ≤ (i : ℕ) := by omega
    rw [dif_neg hpred]
    by_cases h1n : 1 < n
    · have hlt : (i : ℕ) + 1 < n := by omega
      rw [dif_pos hlt, ta_rad_succ_val n p i hlt, h0]
      norm_num
    · have hlt : ¬ (i : ℕ) + 1 < n := by omega
      rw [dif_neg hlt, h0]
      norm_num
      have h2 : ((2 : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        rw [show (2 : ℕ) = n + 1 by omega]
        exact hp
      simpa using h2
  · by_cases hlast : (i : ℕ) + 1 = n
    · have hge : 1 ≤ (i : ℕ) := by omega
      have hlt : (i : ℕ) - 1 < n := by omega
      have hs : ¬ (i : ℕ) + 1 < n := by omega
      rw [dif_neg hs, dif_pos hge, dif_pos hlt]
      rw [ta_rad_pred_val n p i hge hlt, ta_rad_eq]
      have hz : ((i : ℕ) : ZMod p) + 2 = 0 := by
        have hpz : ((n + 1 : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]; exact hp
        have hn : ((n + 1 : ℕ) : ZMod p) = ((i : ℕ) : ZMod p) + 2 := by
          have hnat : n + 1 = (i : ℕ) + 1 + 1 := by omega
          rw [hnat]; push_cast; ring
        rwa [hn] at hpz
      have hsum : 2 * (((i : ℕ) : ZMod p) + 1) + 0 + -((i : ℕ) : ZMod p) =
          ((i : ℕ) : ZMod p) + 2 := by ring
      rw [hsum]
      exact hz
    · have hge : 1 ≤ (i : ℕ) := by omega
      have hlt : (i : ℕ) + 1 < n := by omega
      have hlt2 : (i : ℕ) - 1 < n := by omega
      rw [dif_pos hlt, dif_pos hge, dif_pos hlt2]
      rw [ta_rad_succ_val n p i hlt, ta_rad_pred_val n p i hge hlt2, ta_rad_eq]
      push_cast
      ring

private lemma ta_row_eq_interior (n p : ℕ) (x : Fin n → ZMod p)
    (hx : ∀ i, ∑ j, ggCartanAMod n p i j * x j = 0)
    (r : ℕ) (hr1 : 1 ≤ r) (hr : r + 1 < n) :
    x ⟨r + 1, hr⟩ = 2 * x ⟨r, by omega⟩ - x ⟨r - 1, by omega⟩ := by
  have h := hx ⟨r, by omega⟩
  rw [ta_row_sum] at h
  rw [dif_pos hr, dif_pos hr1] at h
  have h2 : r - 1 < n := by omega
  rw [dif_pos h2] at h
  have hab : 2 * x ⟨r, by omega⟩ - x ⟨r - 1, by omega⟩ = x ⟨r + 1, hr⟩ := by
    have h3 : (2 * x ⟨r, by omega⟩ - x ⟨r - 1, h2⟩) - x ⟨r + 1, hr⟩ = 0 := by
      rw [show (2 * x ⟨r, by omega⟩ + -x ⟨r + 1, hr⟩ + -x ⟨r - 1, h2⟩)
          = ((2 * x ⟨r, by omega⟩ - x ⟨r - 1, h2⟩) - x ⟨r + 1, hr⟩) by ring] at h
      exact h
    rw [sub_eq_zero] at h3
    rw [show (⟨r - 1, h2⟩ : Fin n) = ⟨r - 1, by omega⟩ from Fin.ext rfl] at h3
    exact h3
  exact hab.symm

private def ta_xe (n p : ℕ) (x : Fin n → ZMod p) (t : ℕ) : ZMod p :=
  if h : t < n then x ⟨t, h⟩ else 0

private lemma ta_xe_in {n p : ℕ} (x : Fin n → ZMod p) {t : ℕ} (h : t < n) :
    ta_xe n p x t = x ⟨t, h⟩ := by rw [ta_xe, dif_pos h]

private lemma ta_xe_recur (n p : ℕ) (x : Fin n → ZMod p)
    (hx : ∀ i, ∑ j, ggCartanAMod n p i j * x j = 0)
    (r : ℕ) (hr1 : 1 ≤ r) (hr : r + 1 < n) :
    ta_xe n p x (r + 1) = 2 * ta_xe n p x r - ta_xe n p x (r - 1) := by
  rw [ta_xe_in x (by omega : r + 1 < n), ta_xe_in x (by omega : r < n),
    ta_xe_in x (by omega : r - 1 < n)]
  exact ta_row_eq_interior n p x hx r hr1 hr

private lemma ta_xe_recur_zero (n p : ℕ) (x : Fin n → ZMod p)
    (hx : ∀ i, ∑ j, ggCartanAMod n p i j * x j = 0) (h : 1 < n) :
    ta_xe n p x 1 = 2 * ta_xe n p x 0 := by
  rw [ta_xe_in x (by omega : 1 < n), ta_xe_in x (by omega : 0 < n)]
  have hrow := hx (⟨0, by omega⟩ : Fin n)
  rw [ta_row_sum] at hrow
  rw [dif_pos h, dif_neg (by omega : ¬ 1 ≤ (0 : ℕ))] at hrow
  have h' : 2 * x ⟨0, by omega⟩ - x ⟨1, h⟩ = 0 := by
    rw [show (2 * x ⟨0, by omega⟩ + -x ⟨1, h⟩ + 0)
        = (2 * x ⟨0, by omega⟩ - x ⟨1, h⟩) by ring] at hrow
    exact hrow
  have hadd : 2 * x ⟨0, by omega⟩ = x ⟨1, h⟩ := sub_eq_zero.mp h'
  rw [show (⟨1, h⟩ : Fin n) = ⟨1, by omega⟩ from Fin.ext rfl] at hadd
  exact hadd.symm

private lemma ta_xe_key (n p : ℕ) (x : Fin n → ZMod p)
    (hx : ∀ i, ∑ j, ggCartanAMod n p i j * x j = 0) :
    ∀ m, m < n → ta_xe n p x m = (((m + 1 : ℕ)) : ZMod p) * ta_xe n p x 0 := by
  intro m
  refine Nat.strong_induction_on
    (p := fun k => k < n → ta_xe n p x k = (((k + 1 : ℕ)) : ZMod p) * ta_xe n p x 0) m ?_
  intro k ih hk
  rcases k with _ | _ | k
  · push_cast
    ring
  · rw [ta_xe_recur_zero n p x hx (by omega : 1 < n)]
    push_cast
    ring
  · have hr1 : 1 ≤ k + 1 := by omega
    have hr : (k + 1) + 1 < n := by omega
    rw [ta_xe_recur n p x hx (k + 1) hr1 hr]
    simp only [Nat.add_sub_cancel]
    rw [ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)]
    push_cast
    ring

theorem ggCartanAMod_ker (n p : ℕ) (hn : 1 ≤ n) (x : Fin n → ZMod p)
    (hx : ∀ i, ∑ j, ggCartanAMod n p i j * x j = 0) : x = x ⟨0, hn⟩ • ggCartanARad n p := by
  funext i
  have hi : ta_xe n p x i.val = x i := by
    rw [ta_xe_in x i.isLt]
  rw [← hi, ta_xe_key n p x hx i.val i.isLt, ta_xe_in x hn, Pi.smul_apply, ggCartanARad,
    smul_eq_mul]
  ring

private lemma ta_decomp_col_mul (n p : ℕ) (c : Fin (n - 1) → ZMod p) (j : Fin n)
    (k : Fin (n - 1)) :
    c k * ggCartanAMod n p ⟨k, by omega⟩ j
      = (if (k : ℕ) = (j : ℕ) then c k * 2 else 0)
        + (if (k : ℕ) + 1 = (j : ℕ) then -(c k) else 0)
        + (if (j : ℕ) + 1 = (k : ℕ) then -(c k) else 0) := by
  rw [ggCartanAMod_apply]
  by_cases h1 : (k : ℕ) = (j : ℕ)
  · have hk : (⟨k, by omega⟩ : Fin n) = j := Fin.ext h1
    have h2 : ¬ (k : ℕ) + 1 = (j : ℕ) := by omega
    have h3 : ¬ (j : ℕ) + 1 = (k : ℕ) := by omega
    rw [if_pos hk, if_pos h1, if_neg h2, if_neg h3]; ring
  · have hk : ¬ (⟨k, by omega⟩ : Fin n) = j := fun h => h1 (congrArg Fin.val h)
    by_cases h2 : (k : ℕ) + 1 = (j : ℕ)
    · have h3 : ¬ (j : ℕ) + 1 = (k : ℕ) := by omega
      rw [if_neg hk, if_pos (Or.inl h2), if_neg h1, if_pos h2, if_neg h3]; ring
    · by_cases h3 : (j : ℕ) + 1 = (k : ℕ)
      · rw [if_neg hk, if_pos (Or.inr h3), if_neg h1, if_neg h2, if_pos h3]; ring
      · rw [if_neg hk, if_neg (not_or.mpr ⟨h2, h3⟩), if_neg h1, if_neg h2, if_neg h3]; ring

private lemma ta_col_sum (n p : ℕ) (c : Fin (n - 1) → ZMod p) (j : Fin n) :
    (∑ k : Fin (n - 1), c k * ggCartanAMod n p ⟨k, by omega⟩ j)
      = (if h : (j : ℕ) < n - 1 then c ⟨(j : ℕ), h⟩ * 2 else 0)
        + (if _h : 1 ≤ (j : ℕ) then
             (if h2 : (j : ℕ) - 1 < n - 1 then -(c ⟨(j : ℕ) - 1, h2⟩) else 0)
           else 0)
        + (if h : (j : ℕ) + 1 < n - 1 then -(c ⟨(j : ℕ) + 1, h⟩) else 0) := by
  rw [Finset.sum_congr rfl (fun k _ => ta_decomp_col_mul n p c j k)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [ta_sum_eq_val (f := fun k => c k * 2) (a := (j : ℕ))]
  rw [ta_sum_eq_pred (f := fun k => -(c k)) (a := (j : ℕ))]
  rw [ta_sum_eq_succ (f := fun k => -(c k)) (a := (j : ℕ))]

private def ta_d (n p : ℕ) (c : Fin (n - 1) → ZMod p) (t : ℕ) : ZMod p :=
  if h : t < n - 1 then c ⟨t, h⟩ else 0

private lemma ta_d_out {n p : ℕ} (c : Fin (n - 1) → ZMod p) {t : ℕ} (h : ¬ t < n - 1) :
    ta_d n p c t = 0 := by rw [ta_d, dif_neg h]

private lemma ta_d_base (n p : ℕ) (c : Fin (n - 1) → ZMod p)
    (hc : ∀ j, ∑ k, c k * ggCartanAMod n p ⟨k, by omega⟩ j = 0) :
    ta_d n p c (n - 2) = 0 := by
  by_cases hn : 2 ≤ n
  · have h := hc (⟨n - 1, by omega⟩ : Fin n)
    rw [ta_col_sum] at h
    have h1 : ¬ (n - 1) < n - 1 := by omega
    have h2 : 1 ≤ n - 1 := by omega
    have h3 : (n - 1) - 1 < n - 1 := by omega
    have h4 : ¬ (n - 1) + 1 < n - 1 := by omega
    rw [dif_neg h1, dif_pos h2, dif_pos h3, dif_neg h4] at h
    have hz : -(c ⟨(n - 1) - 1, h3⟩) = 0 := by simpa using h.symm
    have hc' : c ⟨(n - 1) - 1, h3⟩ = 0 := neg_eq_zero.mp hz
    rw [ta_d, dif_pos (show n - 2 < n - 1 by omega)]
    rw [show (⟨n - 2, by omega⟩ : Fin (n - 1)) = ⟨(n - 1) - 1, h3⟩ from
      Fin.ext (by show n - 2 = (n - 1) - 1; omega)]
    exact hc'
  · rw [ta_d, dif_neg (by omega)]

private lemma ta_d_recur (n p : ℕ) (c : Fin (n - 1) → ZMod p)
    (hc : ∀ j, ∑ k, c k * ggCartanAMod n p ⟨k, by omega⟩ j = 0)
    (r : ℕ) (hr : r + 2 < n) :
    ta_d n p c r = 2 * ta_d n p c (r + 1) - ta_d n p c (r + 2) := by
  have h := hc (⟨r + 1, by omega⟩ : Fin n)
  rw [ta_col_sum] at h
  have h1 : r + 1 < n - 1 := by omega
  have h2 : 1 ≤ r + 1 := by omega
  have h3 : (r + 1) - 1 < n - 1 := by omega
  have h' : 2 * ta_d n p c (r + 1) + -ta_d n p c r + -ta_d n p c (r + 2) = 0 := by
    have e1 : c ⟨r + 1, h1⟩ * 2 = 2 * ta_d n p c (r + 1) := by
      rw [ta_d, dif_pos h1]; ring
    have e2 : c ⟨(r + 1) - 1, h3⟩ = ta_d n p c r := by
      rw [ta_d, dif_pos (show r < n - 1 by omega)]
      exact congrArg c (Fin.ext (by show r + 1 - 1 = r; omega))
    by_cases h4 : (r + 1) + 1 < n - 1
    · rw [dif_pos h1, dif_pos h2, dif_pos h3, dif_pos h4] at h
      have e3 : c ⟨(r + 1) + 1, h4⟩ = ta_d n p c (r + 2) := by
        rw [ta_d, dif_pos (show r + 2 < n - 1 by omega)]
      rw [e1, e2, e3] at h
      exact h
    · rw [dif_pos h1, dif_pos h2, dif_pos h3, dif_neg h4] at h
      have e3 : ta_d n p c (r + 2) = 0 := ta_d_out c (by omega)
      rw [e1, e2] at h
      rw [e3]
      simpa using h
  have hcanon : (2 * ta_d n p c (r + 1) - ta_d n p c (r + 2)) - ta_d n p c r = 0 := by
    rw [show (2 * ta_d n p c (r + 1) + -ta_d n p c r + -ta_d n p c (r + 2))
        = ((2 * ta_d n p c (r + 1) - ta_d n p c (r + 2)) - ta_d n p c r) by ring] at h'
    exact h'
  exact (sub_eq_zero.mp hcanon).symm

private lemma ta_rows_dzero (n p : ℕ) (c : Fin (n - 1) → ZMod p)
    (hc : ∀ j, ∑ k, c k * ggCartanAMod n p ⟨k, by omega⟩ j = 0) :
    ∀ m, m ≤ n - 2 → ta_d n p c m = 0 := by
  intro m hm
  exact (Nat.decreasingInduction' (P := fun r => ta_d n p c r = 0 ∧ ta_d n p c (r + 1) = 0)
    (fun k hk _ ih => by
      refine ⟨?_, ih.1⟩
      rw [ta_d_recur n p c hc k (by omega), ih.1, ih.2]
      ring)
    hm ⟨ta_d_base n p c hc, ta_d_out c (by omega)⟩).1

theorem ggCartanAMod_rows_indep (n p : ℕ) (c : Fin (n - 1) → ZMod p)
    (hc : ∀ j, ∑ k, c k * ggCartanAMod n p ⟨k, by omega⟩ j = 0) : c = 0 := by
  funext k
  have hz := ta_rows_dzero n p c hc k.val (by omega)
  rw [ta_d, dif_pos k.isLt] at hz
  exact hz

private lemma ta_edge (n p : ℕ) [Fact p.Prime] (a b : Fin n)
    (h : (a : ℕ) + 1 = (b : ℕ) ∨ (b : ℕ) + 1 = (a : ℕ)) :
    ggCartanAMod n p a b ≠ 0 := by
  rw [ggCartanAMod_apply]
  have hab : a ≠ b := by
    rintro rfl
    rcases h with h | h <;> omega
  rw [if_neg hab, if_pos h]
  exact neg_ne_zero.mpr one_ne_zero

theorem ggCartanAMod_conn (n p : ℕ) [Fact p.Prime] (i j : Fin n) :
    Relation.ReflTransGen (fun a b => ggCartanAMod n p a b ≠ 0) i j := by
  rcases n with _ | n'
  · exact Fin.elim0 i
  · have h0 : ∀ j : Fin (n' + 1),
        Relation.ReflTransGen (fun a b => ggCartanAMod (n' + 1) p a b ≠ 0)
          (0 : Fin (n' + 1)) j := by
      intro j
      have key : ∀ m (hm : m < n' + 1),
          Relation.ReflTransGen (fun a b => ggCartanAMod (n' + 1) p a b ≠ 0)
            (0 : Fin (n' + 1)) ⟨m, hm⟩ := by
        intro m
        induction m with
        | zero => intro hm; exact Relation.ReflTransGen.refl
        | succ m ih =>
          intro hm
          have hm' : m < n' + 1 := by omega
          exact (ih hm').tail (ta_edge (n' + 1) p ⟨m, hm'⟩ ⟨m + 1, hm⟩ (Or.inl rfl))
      exact key j.val j.isLt
    have hlast : ∀ j : Fin (n' + 1),
        Relation.ReflTransGen (fun a b => ggCartanAMod (n' + 1) p a b ≠ 0)
          j (0 : Fin (n' + 1)) := by
      intro j
      have key : ∀ m (hm : m < n' + 1),
          Relation.ReflTransGen (fun a b => ggCartanAMod (n' + 1) p a b ≠ 0)
            ⟨m, hm⟩ (0 : Fin (n' + 1)) := by
        intro m
        induction m with
        | zero => intro hm; exact Relation.ReflTransGen.refl
        | succ m ih =>
          intro hm
          have hm' : m < n' + 1 := by omega
          exact Relation.ReflTransGen.head
            (ta_edge (n' + 1) p ⟨m + 1, hm⟩ ⟨m, hm'⟩ (Or.inr rfl)) (ih hm')
      exact key j.val j.isLt
    exact Relation.ReflTransGen.trans (hlast i) (h0 j)

theorem ggNotDvd_factorial_of_typeA (n p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : p ∣ n + 1)
    (hn : 4 ≤ n) : ¬ p ^ (n - 1) ∣ (n + 1).factorial := by
  obtain ⟨q, hq⟩ := hp
  intro hdiv
  rw [hq] at hdiv
  have hpne1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hpq : p * q ≠ 0 := by rw [← hq]; omega
  have hfac : (p * q).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hle : n - 1 ≤ padicValNat p (p * q).factorial :=
    (Nat.pow_dvd_iff_le_padicValNat hpne1 hfac).mp hdiv
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := p * q) hpq
  have hpge : 2 ≤ p - 1 := by
    have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have h2v : 2 * padicValNat p (p * q).factorial < p * q :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hpge) hlt
  rw [← hq] at hle h2v
  omega

end CFSG.StandardType

end
