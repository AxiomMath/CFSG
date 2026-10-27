module

public import CFSG.RankThree.SubgroupLists.MitchellPairOrder
public import CFSG.RankThree.SubgroupLists.MitchellQOne

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

local notation "⟪" x "⟫" => Units.val x

variable {K : Type} [Field K]

theorem eq_one_or_neg_of_pow_five {x : GL V₄ K} (h5 : x ^ 5 = 1 ∨ x ^ 5 = -1) {j : ℕ}
    (hj1 : 1 ≤ j) (hj5 : j < 5) (hj : x ^ j = 1 ∨ x ^ j = -1) : x = 1 ∨ x = -1 := by
  interval_cases j
  · simpa using hj
  · have h : x = x ^ 5 * ((x ^ 2)⁻¹) ^ 2 := by group
    rcases h5 with h5 | h5 <;> rcases hj with hj | hj <;> rw [h5, hj] at h <;> simp at h <;>
      simp [h]
  · have h : x = (x ^ 3) ^ 2 * (x ^ 5)⁻¹ := by group
    rcases h5 with h5 | h5 <;> rcases hj with hj | hj <;> rw [h5, hj] at h <;> simp at h <;>
      simp [h]
  · have h : x = x ^ 5 * (x ^ 4)⁻¹ := by group
    rcases h5 with h5 | h5 <;> rcases hj with hj | hj <;> rw [h5, hj] at h <;> simp at h <;>
      simp [h]

section Core

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem icosa_triple_core (hp5 : 5 ≤ p) {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) (hneg : (-1 : GL V₄ K) ∈ G) {d e f : GL V₄ K}
    (hdG : d ∈ G) (heG : e ∈ G) (hfG : f ∈ G) (hd : IsNCInv d) (he : IsNCInv e) (hf : IsNCInv f)
    (hθ : 16 * cliffB ⟪d⟫ ⟪e⟫ ^ 4 - 12 * cliffB ⟪d⟫ ⟪e⟫ ^ 2 + 1 = 0)
    (hβ1 : cliffB ⟪d⟫ ⟪e⟫ ^ 2 ≠ 1) (hfP : ∀ a b : K, ⟪f⟫ ≠ a • ⟪d⟫ + b • ⟪e⟫)
    (hγ : cliffB ⟪d⟫ ⟪f⟫ ≠ 0) :
    ((d * e) ^ 5 = 1 ∨ (d * e) ^ 5 = -1) ∧
      (∀ j, 1 ≤ j → j < 5 → (d * e) ^ j ≠ 1 ∧ (d * e) ^ j ≠ -1) ∧
      (∀ j, 1 ≤ j → j < 3 → (d * f) ^ j ≠ 1 ∧ (d * f) ^ j ≠ -1) ∧
      d * e * (d * f) ≠ d * f * (d * e) ∧ d * e * (d * f) ≠ -(d * f * (d * e)) := by
  have hp2 : p ≠ 2 := by omega
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hdM := (mem_cliffSpace_of_involution h2 hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).1
  have heM := (mem_cliffSpace_of_involution h2 he.1 he.2.1 he.2.2.1 he.2.2.2).1
  have hfM := (mem_cliffSpace_of_involution h2 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2).1
  have hdd : ⟪d⟫ * ⟪d⟫ = 1 := by rw [← Units.val_mul, hd.2.1, Units.val_one]
  have hee : ⟪e⟫ * ⟪e⟫ = 1 := by rw [← Units.val_mul, he.2.1, Units.val_one]
  have hff : ⟪f⟫ * ⟪f⟫ = 1 := by rw [← Units.val_mul, hf.2.1, Units.val_one]
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd.2.1
  have hB1 : cliffB ⟪d⟫ ⟪d⟫ = 1 := cliffB_eq_one_of_mul_self h2 hdd
  have hβ : cliffB ⟪d⟫ ⟪e⟫ * cliffB ⟪d⟫ ⟪e⟫ ≠ 1 := by rwa [← sq]
  have h5 := pow_five_eq_one_or_neg_of_quartic h2 hd he hθ
  have hβ0 : cliffB ⟪d⟫ ⟪e⟫ ≠ 0 := by
    intro h0
    rw [h0] at hθ
    norm_num at hθ
  have hDE : ¬ (d * e = 1 ∨ d * e = -1) := by
    rintro (h | h)
    · have : e = d := by
        calc e = d⁻¹ * (d * e) := by group
          _ = d := by rw [h, mul_one, hdinv]
      exact hβ1 (by rw [this, hB1]; norm_num)
    · have : e = -d := by
        calc e = d⁻¹ * (d * e) := by group
          _ = -d := by rw [h, mul_neg_one, hdinv]
      refine hβ1 ?_
      rw [this, Units.val_neg, show (-⟪d⟫ : Matrix V₄ V₄ K) = (-1 : K) • ⟪d⟫ by simp,
        cliffB_smul_right, hB1]
      norm_num
  have hscal : ∀ c : K, ⟪d⟫ * ⟪f⟫ = c • (1 : Matrix V₄ V₄ K) → False := by
    intro c h
    refine hfP c 0 ?_
    calc ⟪f⟫ = ⟪d⟫ * (⟪d⟫ * ⟪f⟫) := by rw [← Matrix.mul_assoc, hdd, Matrix.one_mul]
      _ = c • ⟪d⟫ + (0 : K) • ⟪e⟫ := by
        rw [h, Matrix.mul_smul, Matrix.mul_one, zero_smul, add_zero]
  have hysq := mul_sq_of_isNCInv h2 hd hf
  have hxsq := mul_sq_of_isNCInv h2 hd he
  refine ⟨h5, fun j hj1 hj5 => ?_, fun j hj1 hj3 => ?_, fun hc => ?_, fun hc => ?_⟩
  · have key : ¬ ((d * e) ^ j = 1 ∨ (d * e) ^ j = -1) := fun hj =>
      hDE (eq_one_or_neg_of_pow_five h5 hj1 hj5 hj)
    exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
  · interval_cases j
    · rw [pow_one]
      refine ⟨fun h => hscal 1 ?_, fun h => hscal (-1) ?_⟩
      · rw [one_smul, ← Units.val_mul, h, Units.val_one]
      · rw [neg_one_smul, ← Units.val_mul, h, Units.val_neg, Units.val_one]
    · have h2sc : ∀ ε : K, ⟪d⟫ * ⟪f⟫ * (⟪d⟫ * ⟪f⟫) = ε • (1 : Matrix V₄ V₄ K) → False := by
        intro ε hε
        rw [hysq] at hε
        have h1 : (2 * cliffB ⟪d⟫ ⟪f⟫) • (⟪d⟫ * ⟪f⟫) = (ε + 1) • (1 : Matrix V₄ V₄ K) := by
          rw [add_smul, one_smul, ← hε]
          abel
        refine hscal ((2 * cliffB ⟪d⟫ ⟪f⟫)⁻¹ * (ε + 1)) ?_
        rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ (mul_ne_zero h2 hγ), one_smul]
      have hm : ⟪(d * f) ^ 2⟫ = ⟪d⟫ * ⟪f⟫ * (⟪d⟫ * ⟪f⟫) := by
        rw [Units.val_pow_eq_pow_val, pow_two, Units.val_mul]
      refine ⟨fun h => h2sc 1 ?_, fun h => h2sc (-1) ?_⟩
      · rw [← hm, h, Units.val_one, one_smul]
      · rw [← hm, h, Units.val_neg, Units.val_one, neg_one_smul]
  ·
    have hcm : ⟪d⟫ * ⟪e⟫ * (⟪d⟫ * ⟪f⟫) = ⟪d⟫ * ⟪f⟫ * (⟪d⟫ * ⟪e⟫) := by
      simpa only [Units.val_mul] using congrArg Units.val hc
    have hγ1 : cliffB ⟪d⟫ ⟪f⟫ * cliffB ⟪d⟫ ⟪f⟫ = 1 :=
      cliffB_sq_eq_one_of_commute h2 hdM heM hfM hdd hee hff
        (lin_indep_of_not_mem_span h2 hB1 (cliffB_eq_one_of_mul_self h2 hee) hβ hfP) hcm
    rcases eq_or_eq_neg_of_cliffB_eq_one h2 hU0 hneg hdG hfG hd hf (mul_self_eq_one_iff.mp hγ1)
      with h | h
    · exact hfP 1 0 (by rw [h]; simp)
    · exact hfP (-1) 0 (by rw [h]; simp)
  ·
    obtain ⟨X, hX⟩ : ∃ X : Matrix V₄ V₄ K, X = ⟪d⟫ * ⟪e⟫ := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : Matrix V₄ V₄ K, Y = ⟪d⟫ * ⟪f⟫ := ⟨_, rfl⟩
    rw [← hX] at hxsq
    have hcm : X * Y = -(Y * X) := by
      rw [hX, hY]
      simpa only [Units.val_mul, Units.val_neg] using congrArg Units.val hc
    have hYX0 : Y * X ≠ 0 := by
      have : ⟪d * f * (d * e)⟫ ≠ 0 := Units.ne_zero _
      rwa [Units.val_mul, Units.val_mul, Units.val_mul, ← hX, ← hY] at this
    have hYX : Y * X = -(X * Y) := by rw [hcm, neg_neg]
    have h1 : Y * (X * X) = (X * X) * Y := by
      calc Y * (X * X) = (Y * X) * X := by rw [Matrix.mul_assoc]
        _ = -(X * Y) * X := by rw [hYX]
        _ = -(X * (Y * X)) := by rw [Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(X * -(X * Y)) := by rw [hYX]
        _ = X * (X * Y) := by rw [Matrix.mul_neg, neg_neg]
        _ = (X * X) * Y := by rw [Matrix.mul_assoc]
    rw [hxsq] at h1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    rw [hcm, smul_neg, sub_left_inj] at h1
    have h3 := eq_neg_iff_add_eq_zero.mp h1
    rw [← add_smul] at h3
    rcases smul_eq_zero.mp h3 with h | h
    · have h4 : (2 : K) * (2 * cliffB ⟪d⟫ ⟪e⟫) = 0 := by linear_combination h
      exact hβ0 ((mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left h2)).resolve_left h2)
    · exact hYX0 h

end Core

end CFSG.RankThree.SubgroupLists
