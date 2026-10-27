module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Walter.Ree.Bombieri

open Finset

theorem gap_sum_lt {d : ℕ} (S : Finset ℕ) :
    ∀ M : ℕ, (∀ x ∈ S, x ≤ M) → (∀ x ∈ S, ∀ y ∈ S, x < y → x + d ≤ y) →
      (3 ^ d - 1) * ∑ x ∈ S, 3 ^ x < 3 ^ (M + d) := by
  induction S using Finset.induction_on_max with
  | empty => intro M _ _; simp
  | insert a s hlt ih =>
    intro M hM hgap
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert ha, mul_add]
    have haM : a ≤ M := hM a (mem_insert_self a s)
    have h3 : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
    have hpow : 3 ^ (a + d) = (3 ^ d - 1) * 3 ^ a + 3 ^ a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h3, pow_add, mul_comm]
    have hle : 3 ^ (a + d) ≤ 3 ^ (M + d) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
    · simp only [sum_empty, mul_zero, add_zero]
      calc (3 ^ d - 1) * 3 ^ a < (3 ^ d - 1) * 3 ^ a + 3 ^ a := by
            have : 0 < 3 ^ a := by positivity
            omega
        _ = 3 ^ (a + d) := hpow.symm
        _ ≤ 3 ^ (M + d) := hle
    · have hgap' : ∀ x ∈ s, x + d ≤ a := fun x hx =>
        hgap x (mem_insert_of_mem hx) a (mem_insert_self a s) (hlt x hx)
      have hda : d ≤ a := by have := hgap' x0 hx0; omega
      have ih' := ih (a - d) (fun x hx => by have := hgap' x hx; omega)
        (fun x hx y hy hxy => hgap x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
      rw [Nat.sub_add_cancel hda] at ih'
      calc (3 ^ d - 1) * 3 ^ a + (3 ^ d - 1) * ∑ x ∈ s, 3 ^ x
          < (3 ^ d - 1) * 3 ^ a + 3 ^ a := by omega
        _ = 3 ^ (a + d) := hpow.symm
        _ ≤ 3 ^ (M + d) := hle

theorem three_pow_modEq (m n : ℕ) :
    (3 : ℤ) ^ n ≡ 3 ^ (n % m) [ZMOD (3 ^ m - 1)] := by
  have h1 : (3 : ℤ) ^ m ≡ 1 [ZMOD (3 ^ m - 1)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul]
  calc ((3 : ℤ) ^ m) ^ (n / m) * 3 ^ (n % m) ≡ 1 ^ (n / m) * 3 ^ (n % m) [ZMOD (3 ^ m - 1)] :=
        (h1.pow _).mul_right _
    _ = 3 ^ (n % m) := by rw [one_pow, one_mul]

theorem natCast_modEq_mod (n m : ℕ) : (n : ℤ) ≡ ((n % m : ℕ) : ℤ) [ZMOD m] := by
  rw [Int.natCast_mod]; exact (Int.mod_modEq _ _).symm

theorem lemma3_arith {m t d k : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hk : 1 ≤ k) (a : ℕ → ℤ)
    (ha0 : a 0 ≠ 0) (hab : ∀ i ≤ k, (a i).natAbs + 2 ≤ 3 ^ d)
    (hdiv : ((3 : ℤ) ^ m - 1) ∣ ∑ i ∈ range (k + 1), a i * 3 ^ (t * i)) :
    ∃ l lam : ℕ, 1 ≤ l ∧ l ≤ k ∧ lam < d ∧
      ((t * l : ℤ) ≡ lam [ZMOD m] ∨ (t * l + lam : ℤ) ≡ 0 [ZMOD m]) := by
  by_contra hcon
  push Not at hcon
  set τ : ℕ → ℕ := fun i => (t * i) % m with hτ
  have hτlt : ∀ i, τ i < m := fun i => Nat.mod_lt _ (by omega)
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτm : ∀ i, ((t * i : ℕ) : ℤ) ≡ (τ i : ℤ) [ZMOD m] := fun i => natCast_modEq_mod _ _
  have key : ∀ h j, h ≤ j → ((t * (j - h) : ℕ) : ℤ) ≡ (τ j : ℤ) - τ h [ZMOD m] := by
    intro h j hhj
    have e : ((t * (j - h) : ℕ) : ℤ) = ((t * j : ℕ) : ℤ) - ((t * h : ℕ) : ℤ) := by
      rw [Nat.mul_sub, Nat.cast_sub (Nat.mul_le_mul_left _ hhj)]
    rw [e]
    exact (hτm j).sub (hτm h)
  have gap : ∀ h j, h < j → j ≤ k → τ h + d ≤ τ j ∨ τ j + d ≤ τ h := by
    intro h j hhj hjk
    by_contra hc
    push Not at hc
    rcases le_total (τ h) (τ j) with hle | hle
    · apply (hcon (j - h) (τ j - τ h) (by omega) (by omega) (by omega)).1
      have := key h j hhj.le
      rw [Nat.cast_mul] at this
      rw [Nat.cast_sub hle]
      exact this
    · apply (hcon (j - h) (τ h - τ j) (by omega) (by omega) (by omega)).2
      have := (key h j hhj.le).add_right ((τ h : ℤ) - τ j)
      rw [Nat.cast_mul] at this
      rw [Nat.cast_sub hle]
      simpa using this
  have hinj : Set.InjOn τ (range (k + 1)) := by
    intro h hh j hj hτhj
    simp only [coe_range, Set.mem_Iio] at hh hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := gap h j hlt (by omega); omega
    · have := gap j h hlt (by omega); omega
  set S := (range (k + 1)).image τ with hS
  have hSne : S.Nonempty := ⟨τ 0, mem_image_of_mem _ (by simp)⟩
  set M := S.max' hSne with hM
  obtain ⟨jm, hjm, hjmM⟩ := mem_image.mp (S.max'_mem hSne)
  have hjm' : jm ≤ k := by simp at hjm; omega
  have hτ1 : d ≤ τ 1 := by
    rcases gap 0 1 (by norm_num) hk with h | h <;> omega
  have hMτ : ∀ i ≤ k, τ i ≤ M := fun i hi => S.le_max' _ (mem_image_of_mem _ (by simp; omega))
  have hjm0 : jm ≠ 0 := by
    rintro rfl
    have := hMτ 1 hk
    omega
  by_cases hbig : m < M + d
  · apply (hcon jm (m - M) (Nat.one_le_iff_ne_zero.mpr hjm0) hjm' (by omega)).2
    have h1 := hτm jm
    rw [hjmM] at h1
    have : ((m - M : ℕ) : ℤ) = m - M := Nat.cast_sub (by have := hτlt jm; omega)
    rw [this]
    calc (t * jm + (m - M) : ℤ) ≡ M + (m - M) [ZMOD m] := by
          have := h1.add_right ((m : ℤ) - M); push_cast at this ⊢; exact this
      _ = m := by ring
      _ ≡ 0 [ZMOD m] := by rw [Int.modEq_zero_iff_dvd]
  · push Not at hbig
    set A := ∑ i ∈ range (k + 1), a i * 3 ^ τ i with hA
    have hAdiv : ((3 : ℤ) ^ m - 1) ∣ A := by
      have h1 : ((3 : ℤ) ^ m - 1) ∣ (∑ i ∈ range (k + 1), a i * 3 ^ (t * i)) - A := by
        rw [hA, ← sum_sub_distrib]
        refine dvd_sum fun i _ => ?_
        rw [← mul_sub]
        exact Dvd.dvd.mul_left (Int.ModEq.dvd (three_pow_modEq m (t * i)).symm) _
      have := dvd_sub hdiv h1
      simpa using this
    have hgapS : ∀ x ∈ S, ∀ y ∈ S, x < y → x + d ≤ y := by
      intro x hx y hy hxy
      obtain ⟨h, hh, rfl⟩ := mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hy
      simp only [mem_range] at hh hj
      rcases Nat.lt_trichotomy h j with hlt | heq | hlt
      · rcases gap h j hlt (by omega) with g | g <;> omega
      · subst heq; omega
      · rcases gap j h hlt (by omega) with g | g <;> omega
    have hsumS : ∑ i ∈ range (k + 1), (3 : ℕ) ^ τ i = ∑ x ∈ S, 3 ^ x :=
      (sum_image hinj).symm
    have hgs := gap_sum_lt S M (fun x hx => S.le_max' x hx) hgapS
    have hS1 : 1 ≤ ∑ x ∈ S, (3 : ℕ) ^ x := by
      obtain ⟨x, hx⟩ := hSne
      exact (Nat.one_le_pow _ _ (by norm_num)).trans (single_le_sum (fun _ _ => by positivity) hx)
    have hpowle : (3 : ℕ) ^ (M + d) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hbig
    have hbound : A.natAbs ≤ 3 ^ m - 2 := by
      calc A.natAbs ≤ ∑ i ∈ range (k + 1), (a i * 3 ^ τ i).natAbs := Int.natAbs_sum_le _ _
        _ = ∑ i ∈ range (k + 1), (a i).natAbs * 3 ^ τ i := by
            refine sum_congr rfl fun i _ => ?_
            rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
        _ ≤ ∑ i ∈ range (k + 1), (3 ^ d - 2) * 3 ^ τ i := by
            refine sum_le_sum fun i hi => Nat.mul_le_mul_right _ ?_
            have := hab i (by simp at hi; omega); omega
        _ = (3 ^ d - 2) * ∑ x ∈ S, 3 ^ x := by rw [← mul_sum, hsumS]
        _ ≤ 3 ^ m - 2 := by
            have h3 : 2 ≤ 3 ^ d := by
              have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hd
              simpa using this.trans' (by norm_num)
            have e : (3 ^ d - 2) * ∑ x ∈ S, 3 ^ x + ∑ x ∈ S, 3 ^ x =
                (3 ^ d - 1) * ∑ x ∈ S, 3 ^ x := by
              rw [← Nat.succ_mul]; congr 1; omega
            omega
    have hm1 : ((3 : ℤ) ^ m - 1).natAbs = 3 ^ m - 1 := by
      have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have : ((3 : ℤ) ^ m - 1) = ((3 ^ m - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub h1]; push_cast; ring
      rw [this, Int.natAbs_natCast]
    have hA0 : A = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hAdiv (by
      rw [hm1]
      have : 3 ≤ 3 ^ m := Nat.le_self_pow (by omega) 3
      omega)
    have hdvd : (3 : ℤ) ^ d ∣ a 0 := by
      have h1 : A = ∑ i ∈ range k, a (i + 1) * 3 ^ τ (i + 1) + a 0 := by
        rw [hA, sum_range_succ', hτ0, pow_zero, mul_one]
      have h2 : (3 : ℤ) ^ d ∣ ∑ i ∈ range k, a (i + 1) * 3 ^ τ (i + 1) := by
        refine dvd_sum fun i hi => Dvd.dvd.mul_left (pow_dvd_pow 3 ?_) _
        simp only [mem_range] at hi
        rcases gap 0 (i + 1) (by omega) (by omega) with g | g <;> omega
      have : a 0 = A - ∑ i ∈ range k, a (i + 1) * 3 ^ τ (i + 1) := by rw [h1]; ring
      rw [this, hA0, zero_sub]
      exact (dvd_neg).mpr h2
    have hle := Int.natAbs_le_of_dvd_ne_zero hdvd ha0
    have := hab 0 (by omega)
    rw [Int.natAbs_pow] at hle
    simp at hle
    omega

end CFSG.Walter.Ree.Bombieri
