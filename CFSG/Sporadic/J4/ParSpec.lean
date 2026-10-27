module

public import Mathlib
public import Certificates.Data.CFSGNative.J4.Store

public section

namespace CFSG.Sporadic.J4

open Native

theorem allFrom_eq_true {p : ℕ → Bool} :
    ∀ {lo k : ℕ}, allFrom p lo k = true → ∀ i, lo ≤ i → i < lo + k → p i = true
  | _, 0, _, _, h1, h2 => by omega
  | lo, k + 1, h, i, h1, h2 => by
    rw [allFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact allFrom_eq_true h.2 i h1 (by omega)

theorem parAllS_eq_true {n chunks : ℕ} {p : ℕ → Bool} (h : parAllS n chunks p = true) :
    ∀ i < n, p i = true := by
  intro i hi
  unfold parAllS at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  have hdm := Nat.div_add_mod (n + chunks) (chunks + 1)
  have hmod := Nat.mod_lt (n + chunks) (by omega : 0 < chunks + 1)
  have hcov : n ≤ chunkLen n chunks * (chunks + 1) := by
    unfold chunkLen
    rw [Nat.mul_comm]
    omega
  have hpos : 0 < chunkLen n chunks := by
    rcases Nat.eq_zero_or_pos (chunkLen n chunks) with h0 | h0
    · rw [h0, Nat.zero_mul] at hcov; omega
    · exact h0
  generalize chunkLen n chunks = len at hcov hpos h
  have hj : i / len < chunks + 1 := by
    rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm]; omega
  have := h (i / len) hj
  change allFrom p (i / len * len) (min n (i / len * len + len) - i / len * len) = true at this
  have h1 : i / len * len ≤ i := Nat.div_mul_le_self i len
  have h2 : i < i / len * len + len := by
    have := Nat.lt_div_mul_add (a := i) hpos
    omega
  exact allFrom_eq_true this i h1 (by omega)

theorem allStepFrom_eq_true {p : ℕ → Bool} {c : ℕ} :
    ∀ {i k : ℕ}, allStepFrom p i c k = true → ∀ t < k, p (i + c * t) = true
  | _, 0, _, _, ht => absurd ht (Nat.not_lt_zero _)
  | i, k + 1, h, t, ht => by
    rw [allStepFrom, Bool.and_eq_true] at h
    cases t with
    | zero => simpa using h.1
    | succ t =>
      have := allStepFrom_eq_true h.2 t (by omega)
      rwa [show i + c + c * t = i + c * (t + 1) by ring] at this

theorem parAllR_eq_true {n chunks : ℕ} {p : ℕ → Bool} (h : parAllR n chunks p = true) :
    ∀ i < n, p i = true := by
  intro i hi
  unfold parAllR at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  have hcpos : 0 < chunks + 1 := Nat.succ_pos _
  have hstep := h (i % (chunks + 1)) (Nat.mod_lt _ hcpos)
  change allStepFrom p (i % (chunks + 1)) (chunks + 1)
    ((n + (chunks + 1) - 1 - i % (chunks + 1)) / (chunks + 1)) = true at hstep
  have hdiv := Nat.mod_add_div i (chunks + 1)
  have hk : i / (chunks + 1) < (n + (chunks + 1) - 1 - i % (chunks + 1)) / (chunks + 1) := by
    apply Nat.lt_of_succ_le
    rw [Nat.le_div_iff_mul_le hcpos]
    have hmod := Nat.mod_lt i hcpos
    have e : (i / (chunks + 1) + 1) * (chunks + 1) =
        (chunks + 1) * (i / (chunks + 1)) + (chunks + 1) := by ring
    rw [e]
    generalize (chunks + 1) * (i / (chunks + 1)) = X at hdiv ⊢
    omega
  have := allStepFrom_eq_true hstep _ hk
  rwa [hdiv] at this

end CFSG.Sporadic.J4
