module

public import Mathlib

public section

namespace CFSG.StandardType

open Finset
open scoped BigOperators


theorem ggNSLiePI2_seq_bound {K : Type*} [Field K] (n : ℕ) (a b c : ℕ → K)
    (hc : ∀ i, n ≤ i → c i = 0)
    (ha : ∀ i, i < n - 1 → a i ≠ 0)
    (hab : ∀ i, i < n - 1 → a i * b i = 1)
    (h0 : 2 * c 0 + a 0 * c 1 = 0)
    (hrow : ∀ i, 1 ≤ i → i < n → b (i - 1) * c (i - 1) + 2 * c i + a i * c (i + 1) = 0) :
    (n + 1 : K) * c 0 = 0 := by
  let lam : ℕ → K := fun k => (-1 : K) ^ k * (Finset.range k).prod a
  let e : ℕ → K := fun k => lam k * c k
  have hlam0 : lam 0 = 1 := by simp [lam]
  have hlam : ∀ k, lam (k + 1) = -lam k * a k := by
    intro k
    simp only [lam, Finset.prod_range_succ, pow_succ]
    ring
  have he0 : e 0 = c 0 := by simp [e, hlam0]
  have hl1 : lam 1 = -a 0 := by
    have h := hlam 0
    rw [hlam0] at h
    simpa using h
  have he1 : e 1 = 2 * e 0 := by
    have ha0 : a 0 * c 1 = -(2 * c 0) := by
      rw [add_comm] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have h : e 1 = -(a 0 * c 1) := by
      rw [show e 1 = lam 1 * c 1 from rfl, hl1]
      ring
    rw [h, ha0, he0]
    ring
  have hrec : ∀ k, 1 ≤ k → k < n → e (k + 1) = 2 * e k - e (k - 1) := by
    intro k hk1 hkn
    have hk0 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk1
    have hlamk : lam k = -lam (k - 1) * a (k - 1) := by
      conv_lhs => rw [← hk0]
      rw [hlam]
    have hhab : a (k - 1) * b (k - 1) = 1 := by apply hab; omega
    have haux : a k * c (k + 1) = -(b (k - 1) * c (k - 1) + 2 * c k) := by
      linear_combination hrow k hk1 hkn
    have h1 : e (k + 1) = lam k * (b (k - 1) * c (k - 1) + 2 * c k) := by
      have hh : e (k + 1) = -lam k * (a k * c (k + 1)) := by
        rw [show e (k + 1) = lam (k + 1) * c (k + 1) from rfl, hlam]
        ring
      rw [hh, haux]
      ring
    have h2 : lam k * (b (k - 1) * c (k - 1) + 2 * c k) = 2 * e k - e (k - 1) := by
      rw [show e k = lam k * c k from rfl, show e (k - 1) = lam (k - 1) * c (k - 1) from rfl,
        hlamk]
      linear_combination (-(lam (k - 1) * c (k - 1))) * hhab
    rw [h1, h2]
  have hmain : ∀ k, k ≤ n - 1 → e k = (k + 1 : K) * e 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases k with _ | k'
      · rw [he0]; norm_num
      · rcases k' with _ | k''
        · rw [he1]; norm_num
        · have hlt : k'' + 1 < n := by omega
          have hrec' := hrec (k'' + 1) (by omega) hlt
          rw [show k'' + 1 - 1 = k'' from by omega] at hrec'
          rw [hrec', ih (k'' + 1) (by omega) (by omega), ih k'' (by omega) (by omega)]
          push_cast
          ring
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simpa using hc 0 (by omega)
    · have hc1 : c 1 = 0 := hc 1 (by omega)
      have h0' : (2 : K) * c 0 = 0 := by simpa [hc1] using h0
      linear_combination h0'
  · have hrowlast := hrow (n - 1) (by omega) (by omega)
    have hcn : c n = 0 := hc n (by omega)
    have hstep : b (n - 2) * c (n - 2) + 2 * c (n - 1) = 0 := by
      have h1 : n - 1 - 1 = n - 2 := by omega
      have h2 : n - 1 + 1 = n := by omega
      rw [h1, h2, hcn, mul_zero, add_zero] at hrowlast
      exact hrowlast
    have hhab : a (n - 2) * b (n - 2) = 1 := by apply hab; omega
    have hlamn : lam (n - 1) = -lam (n - 2) * a (n - 2) := by
      have h1 : n - 1 = (n - 2) + 1 := by omega
      conv_lhs => rw [h1]
      rw [hlam]
    have hkey : e (n - 2) = 2 * e (n - 1) := by
      have hmul := congrArg (fun x => lam (n - 1) * x) hstep
      rw [mul_add, mul_zero] at hmul
      have hb : lam (n - 1) * (b (n - 2) * c (n - 2)) = -e (n - 2) := by
        rw [hlamn, show e (n - 2) = lam (n - 2) * c (n - 2) from rfl]
        linear_combination (-(lam (n - 2) * c (n - 2))) * hhab
      have h2 : lam (n - 1) * (2 * c (n - 1)) = 2 * e (n - 1) := by
        rw [show e (n - 1) = lam (n - 1) * c (n - 1) from rfl]; ring
      rw [hb, h2] at hmul
      linear_combination (-1 : K) * hmul
    have h1 := hmain (n - 2) (by omega)
    have h2 := hmain (n - 1) (by omega)
    rw [h1, h2] at hkey
    have hcast1 : ((n - 2 : ℕ) : K) + 1 = (n : K) - 1 := by
      have h : (n : K) = ((n - 2 : ℕ) : K) + 2 := by
        have h2 : n = (n - 2) + 2 := by omega
        rw [h2]; push_cast; ring
      rw [h]; ring
    have hcast2 : ((n - 1 : ℕ) : K) + 1 = (n : K) := by
      have h2 : n = (n - 1) + 1 := by omega
      rw [h2]; push_cast; ring
    rw [hcast1, hcast2] at hkey
    have hfin : (n + 1 : K) * e 0 = 0 := by
      linear_combination (-1 : K) * hkey
    rwa [he0] at hfin



open Finset
open scoped BigOperators

lemma ggNSLiePI2_sum_band {K : Type*} [AddCommMonoid K] {n : ℕ} (g : Fin n → K) (i : Fin n)
    (h : ∀ j : Fin n, j ≠ i → (j : ℕ) ≠ (i : ℕ) + 1 → (i : ℕ) ≠ (j : ℕ) + 1 → g j = 0) :
    (Finset.univ : Finset (Fin n)).sum g = g i
      + (if hh : (i : ℕ) + 1 < n then g ⟨(i : ℕ) + 1, hh⟩ else 0)
      + (if hh : 0 < (i : ℕ) then g ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
          else 0) := by
  have hmem : ∀ a : Fin n, a ∈ (Finset.univ : Finset (Fin n)) := fun a => Finset.mem_univ a
  have hpred_ne_i : ∀ (hh0 : 0 < (i : ℕ)),
      (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n) ≠ i := by
    intro hh0 hh
    have h2 := congrArg (fun x : Fin n => (x : ℕ)) hh
    simp only [Fin.val_mk, Fin.eta] at h2
    omega
  have hpred_ne_succ : ∀ (hh0 : 0 < (i : ℕ)) (hh1 : (i : ℕ) + 1 < n),
      (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n)
        ≠ (⟨(i : ℕ) + 1, hh1⟩ : Fin n) := by
    intro hh0 hh1 hh
    have h2 := congrArg (fun x : Fin n => (x : ℕ)) hh
    simp only [Fin.val_mk] at h2
    omega
  have hsucc_ne_i : ∀ (hh1 : (i : ℕ) + 1 < n),
      (⟨(i : ℕ) + 1, hh1⟩ : Fin n) ≠ i := by
    intro hh1 hh
    have h2 := congrArg (fun x : Fin n => (x : ℕ)) hh
    simp only [Fin.val_mk, Fin.eta] at h2
    omega
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin n)) g (hmem i)]
  by_cases hh1 : (i : ℕ) + 1 < n
  · have hmem1 : (⟨(i : ℕ) + 1, hh1⟩ : Fin n) ∈ Finset.univ.erase i := by
      rw [Finset.mem_erase]; exact ⟨hsucc_ne_i hh1, hmem _⟩
    rw [← Finset.sum_erase_add (Finset.univ.erase i) g hmem1]
    rw [dif_pos hh1]
    by_cases hh0 : 0 < (i : ℕ)
    · rw [dif_pos hh0]
      have hmem2 : (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n) ∈
          (Finset.univ.erase i).erase (⟨(i : ℕ) + 1, hh1⟩ : Fin n) := by
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨hpred_ne_succ hh0 hh1, hpred_ne_i hh0, hmem _⟩
      rw [Finset.sum_eq_single
        (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n) ?_ ?_]
      · abel
      · intro b hb hbne
        rw [Finset.mem_erase, Finset.mem_erase] at hb
        refine h b hb.2.1 ?_ ?_
        · intro hv
          exact hb.1 (Fin.ext hv)
        · intro hv
          exact hbne (Fin.ext (by simp only [Fin.val_mk]; omega))
      · intro hbnot; exact absurd hmem2 hbnot
    · rw [dif_neg hh0]
      have hzero : ((Finset.univ.erase i).erase (⟨(i : ℕ) + 1, hh1⟩ : Fin n)).sum g = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [Finset.mem_erase, Finset.mem_erase] at hb
        refine h b hb.2.1 ?_ ?_
        · intro hv
          exact hb.1 (Fin.ext hv)
        · intro hv; omega
      rw [hzero]; abel
  · rw [dif_neg hh1]
    by_cases hh0 : 0 < (i : ℕ)
    · rw [dif_pos hh0]
      have hmem2 : (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n) ∈
          Finset.univ.erase i := by
        rw [Finset.mem_erase]; exact ⟨hpred_ne_i hh0, hmem _⟩
      rw [Finset.sum_eq_single
        (⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ : Fin n) ?_ ?_]
      · abel
      · intro b hb hbne
        rw [Finset.mem_erase] at hb
        refine h b hb.1 ?_ ?_
        · intro hv; omega
        · intro hv
          exact hbne (Fin.ext (by simp only [Fin.val_mk]; omega))
      · intro hbnot; exact absurd hmem2 hbnot
    · rw [dif_neg hh0]
      have hzero : (Finset.univ.erase i).sum g = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [Finset.mem_erase] at hb
        refine h b hb.1 ?_ ?_
        · intro hv; omega
        · intro hv; omega
      rw [hzero]; abel


end CFSG.StandardType
