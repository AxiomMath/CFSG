module

public import CFSG.Quasithin.EmptyFaithful.S151ZM

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {n : ℕ}

theorem wd_xgx_zero {a : ℕ} {g X : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hX : ∀ p q : Fin n, ¬ ((p : ℕ) < a ∧ a ≤ (q : ℕ)) → X p q = 0) (hg : BCond n a g) :
    X * g * X = 0 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases h1 : (p : ℕ) < a ∧ a ≤ (r : ℕ)
  · by_cases h2 : (s : ℕ) < a ∧ a ≤ (q : ℕ)
    · rw [hg r s h1.2 h2.1]
      simp
    · rw [hX s q h2]
      simp
  · rw [hX p r h1]
    simp

theorem wd_sub_one_of_mem_Tgrp {a : ℕ} {t : SLt n} (ht : t ∈ Tgrp n a) (p q : Fin n)
    (h : ¬ ((p : ℕ) < a ∧ a ≤ (q : ℕ))) : (mat t - 1) p q = 0 := by
  have := ht p q h
  simp only [Matrix.sub_apply, this, sub_self]

theorem wd_mat_comm_of_mem_Tgrp {a : ℕ} {t g : SLt n} (ht : t ∈ Tgrp n a)
    (hg : g ∈ stabilizer (flagSpace n (ZMod 2) a)) :
    mat ⁅t, g⁆ = 1 + (mat t - 1) + mat g * (mat t - 1) * mat g⁻¹ := by
  have hX := wd_sub_one_of_mem_Tgrp ht
  have hgb := bcond_of_mem_stabilizer hg
  have hxgx := wd_xgx_zero (a := a) hX hgb
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (Tgrp_sq ht)
  have hgg : mat g * mat g⁻¹ = 1 := mat_mul_inv g
  rw [commutatorElement_def, hinv, mat_mul, mat_mul, mat_mul]
  set X := mat t - 1 with hXdef
  have ht' : mat t = 1 + X := by rw [hXdef]; abel
  rw [ht']
  have e : (1 + X) * mat g * (1 + X) * mat g⁻¹ =
      mat g * mat g⁻¹ + X * (mat g * mat g⁻¹) + mat g * X * mat g⁻¹ + X * mat g * X * mat g⁻¹ := by
    noncomm_ring
  rw [e, hgg, hxgx]
  simp

theorem wd_mat_mul_single_mul_apply (G H : Matrix (Fin n) (Fin n) (ZMod 2)) (j k p q : Fin n) :
    (G * Matrix.single j k (1 : ZMod 2) * H) p q = G p j * H k q := by
  rw [Matrix.mul_apply]
  have h1 : ∀ x : Fin n, (G * Matrix.single j k (1 : ZMod 2)) p x = if k = x then G p j else 0 := by
    intro x
    rw [Matrix.mul_apply]
    simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero]
    by_cases hx : k = x
    · simp [hx]
    · simp [hx]
  simp only [h1, ite_mul, zero_mul]
  simp

theorem wd_mat_comm_tvec_apply {a : ℕ} {j k : Fin n} (hj : (j : ℕ) < a) (hk : a ≤ (k : ℕ))
    (hjk : j ≠ k) {g : SLt n} (hg : g ∈ stabilizer (flagSpace n (ZMod 2) a)) (p q : Fin n) :
    mat ⁅tvec j k hjk, g⁆ p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q +
      (if j = p ∧ k = q then 1 else 0) + mat g p j * mat g⁻¹ k q := by
  rw [wd_mat_comm_of_mem_Tgrp (tvec_mem_Tgrp hj hk hjk) hg, mat_tvec]
  have e : (1 + Matrix.single j k (1 : ZMod 2)) - 1 = Matrix.single j k 1 := by abel
  rw [e]
  simp only [Matrix.add_apply, wd_mat_mul_single_mul_apply, Matrix.single_apply]

theorem wd_comm_tvec_entries {a b : ℕ} {j k : Fin n} (hj : (j : ℕ) < a) (hk : a ≤ (k : ℕ))
    (hjk : j ≠ k) {g : SLt n} (hg : g ∈ stabilizer (flagSpace n (ZMod 2) a))
    (hmem : ⁅tvec j k hjk, g⁆ ∈ Tgrp n b) (p q : Fin n) (hpq : ¬ ((p : ℕ) < b ∧ b ≤ (q : ℕ))) :
    mat g p j * mat g⁻¹ k q = if j = p ∧ k = q then 1 else 0 := by
  have h1 : mat ⁅tvec j k hjk, g⁆ p q = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p q := hmem p q hpq
  rw [wd_mat_comm_tvec_apply hj hk hjk hg] at h1
  have h2 : (if j = p ∧ k = q then (1 : ZMod 2) else 0) + mat g p j * mat g⁻¹ k q = 0 := by
    have := h1
    rw [add_assoc] at this
    exact add_eq_left.mp this
  exact (CharTwo.add_eq_zero.mp h2).symm

theorem wd_zmod2_mul_eq_one : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide

def wd_blk (a b : ℕ) (i : Fin n) : ℕ := if (i : ℕ) < a then 0 else if (i : ℕ) < b then 1 else 2

theorem wd_blk_le (a b : ℕ) (i : Fin n) : wd_blk a b i ≤ 2 := by
  unfold wd_blk
  split_ifs <;> omega

theorem wd_eq_one_of_comm_mem {a b : ℕ} (ha : 0 < a) (hab : a < b) (hbn : b < n) {g : SLt n}
    (hga : g ∈ stabilizer (flagSpace n (ZMod 2) a)) (hgb : g ∈ stabilizer (flagSpace n (ZMod 2) b))
    (hA : ∀ t ∈ Tgrp n a, ⁅t, g⁆ ∈ Tgrp n b) (hB : ∀ t ∈ Tgrp n b, ⁅t, g⁆ ∈ Tgrp n a)
    (hg3 : g ^ 3 = 1) : g = 1 := by
  set G : Matrix (Fin n) (Fin n) (ZMod 2) := mat g with hG
  set H : Matrix (Fin n) (Fin n) (ZMod 2) := mat g⁻¹ with hH
  have hHG : H * G = 1 := by
    rw [hH, hG, ← mat_mul, inv_mul_cancel, mat_one]
  have hn0 : 0 < n := by omega
  let j₀ : Fin n := ⟨0, hn0⟩
  let k₀ : Fin n := ⟨a, by omega⟩
  have F1 : ∀ (j k : Fin n), (j : ℕ) < a → a ≤ (k : ℕ) → ∀ p q : Fin n,
      ¬ ((p : ℕ) < b ∧ b ≤ (q : ℕ)) → G p j * H k q = if j = p ∧ k = q then 1 else 0 := by
    intro j k hj hk p q hpq
    have hjk : j ≠ k := fun h => by rw [h] at hj; omega
    exact wd_comm_tvec_entries hj hk hjk hga (hA _ (tvec_mem_Tgrp hj hk hjk)) p q hpq
  have F2 : ∀ (j k : Fin n), (j : ℕ) < b → b ≤ (k : ℕ) → ∀ p q : Fin n,
      ¬ ((p : ℕ) < a ∧ a ≤ (q : ℕ)) → G p j * H k q = if j = p ∧ k = q then 1 else 0 := by
    intro j k hj hk p q hpq
    have hjk : j ≠ k := fun h => by rw [h] at hj; omega
    exact wd_comm_tvec_entries (a := b) (b := a) hj hk hjk hgb (hB _ (tvec_mem_Tgrp hj hk hjk)) p q hpq
  have hj₀ : ((j₀ : Fin n) : ℕ) < a := by show 0 < a; exact ha
  have hk₀ : a ≤ ((k₀ : Fin n) : ℕ) := le_rfl
  have hk₀b : ((k₀ : Fin n) : ℕ) < b := hab
  have hHkk : ∀ k : Fin n, a ≤ (k : ℕ) → (k : ℕ) < b → H k k = 1 := by
    intro k hk1 hk2
    have h := F1 j₀ k hj₀ hk1 j₀ k (by omega)
    simp only [and_self, ite_true] at h
    exact (wd_zmod2_mul_eq_one _ _ h).2
  have hGj₀ : G j₀ j₀ = 1 := by
    have h := F1 j₀ k₀ hj₀ hk₀ j₀ k₀ (by show ¬ ((0 : ℕ) < b ∧ b ≤ a); omega)
    simp only [and_self, ite_true] at h
    exact (wd_zmod2_mul_eq_one _ _ h).1
  have hGcol : ∀ j : Fin n, (j : ℕ) < a → ∀ p : Fin n, G p j = if j = p then 1 else 0 := by
    intro j hj p
    have h := F1 j k₀ hj hk₀ p k₀ (by show ¬ ((p : ℕ) < b ∧ b ≤ a); omega)
    rw [hHkk k₀ hk₀ hk₀b, mul_one] at h
    simpa using h
  have hHrow2 : ∀ k : Fin n, a ≤ (k : ℕ) → (k : ℕ) < b → ∀ q : Fin n, (q : ℕ) < b →
      H k q = if k = q then 1 else 0 := by
    intro k hk1 hk2 q hq
    have h := F1 j₀ k hj₀ hk1 j₀ q (by show ¬ ((0 : ℕ) < b ∧ b ≤ (q : ℕ)); omega)
    rw [hGj₀, one_mul] at h
    simpa using h
  have hGk₀ : G k₀ k₀ = 1 := by
    have hk₁ : b ≤ ((⟨b, hbn⟩ : Fin n) : ℕ) := le_rfl
    have h := F2 k₀ ⟨b, hbn⟩ hk₀b hk₁ k₀ ⟨b, hbn⟩ (by show ¬ ((a : ℕ) < a ∧ a ≤ b); omega)
    simp only [and_self, ite_true] at h
    exact (wd_zmod2_mul_eq_one _ _ h).1
  have hHrow3 : ∀ k : Fin n, b ≤ (k : ℕ) → ∀ q : Fin n, H k q = if k = q then 1 else 0 := by
    intro k hk q
    have h := F2 k₀ k hk₀b hk k₀ q (by show ¬ ((a : ℕ) < a ∧ a ≤ (q : ℕ)); omega)
    rw [hGk₀, one_mul] at h
    simpa using h
  have hHcol : ∀ j : Fin n, (j : ℕ) < a → ∀ p : Fin n,
      H p j = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) p j := by
    intro j hj p
    have h := congrFun (congrFun hHG p) j
    rw [Matrix.mul_apply] at h
    have h2 : ∀ s : Fin n, H p s * G s j = if j = s then H p s else 0 := by
      intro s
      rw [hGcol j hj s]
      split_ifs <;> simp
    simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
    exact h
  set N : Matrix (Fin n) (Fin n) (ZMod 2) := H - 1 with hNdef
  have hN : ∀ p q : Fin n, ¬ wd_blk a b p < wd_blk a b q → N p q = 0 := by
    intro p q hpq
    have key : ((q : ℕ) < a) ∨ (a ≤ (q : ℕ) ∧ (q : ℕ) < b ∧ a ≤ (p : ℕ)) ∨
        (b ≤ (q : ℕ) ∧ b ≤ (p : ℕ)) := by
      unfold wd_blk at hpq
      split_ifs at hpq <;> omega
    simp only [hNdef, Matrix.sub_apply]
    rcases key with h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · rw [hHcol q h p, sub_self]
    · by_cases hp2 : (p : ℕ) < b
      · rw [hHrow2 p h3 hp2 q h2, Matrix.one_apply, sub_self]
      · rw [hHrow3 p (by omega) q, Matrix.one_apply, sub_self]
    · rw [hHrow3 p h2 q, Matrix.one_apply, sub_self]
  have hN3 : N * N * N = 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_contra hne
    have h1 : N p r ≠ 0 := fun h => hne (by rw [h]; simp)
    have h2 : N r s ≠ 0 := fun h => hne (by rw [h]; simp)
    have h3 : N s q ≠ 0 := fun h => hne (by rw [h]; simp)
    have e1 : wd_blk a b p < wd_blk a b r := by_contra fun h => h1 (hN p r h)
    have e2 : wd_blk a b r < wd_blk a b s := by_contra fun h => h2 (hN r s h)
    have e3 : wd_blk a b s < wd_blk a b q := by_contra fun h => h3 (hN s q h)
    have := wd_blk_le a b q
    omega
  have hHN : H = 1 + N := by rw [hNdef]; abel
  have hNN : N + N = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hNNNN : N * N + N * N = 0 := by
    ext p q
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hH4 : H * H * (H * H) = 1 := by
    have e2 : H * H = 1 + N * N := by
      calc H * H = (1 + N) * (1 + N) := by rw [← hHN]
        _ = 1 + (N + N) + N * N := by noncomm_ring
        _ = 1 + N * N := by rw [hNN]; simp
    rw [e2]
    calc (1 + N * N) * (1 + N * N) = 1 + (N * N + N * N) + (N * N * N) * N := by noncomm_ring
      _ = 1 := by rw [hNNNN, hN3]; simp
  have hg4 : g ^ 4 = 1 := by
    have h : (g⁻¹) ^ 4 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow]
      show H ^ 4 = 1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact hH4
    rw [inv_pow, inv_eq_one] at h
    exact h
  calc g = g ^ 4 * (g ^ 3)⁻¹ := by group
    _ = 1 := by rw [hg4, hg3]; simp

end CFSG.Quasithin.FLc
