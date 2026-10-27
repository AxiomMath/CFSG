module

import Mathlib.Tactic.NormNum.Prime
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessTrace
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix
open scoped MatrixGroups

theorem mem_of_prime_dvd_prod {p : ℕ} (hp : p.Prime) :
    ∀ (l : List ℕ), (∀ q ∈ l, q.Prime) → p ∣ l.prod → p ∈ l
  | [], _, h => absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
  | q :: l, hl, h => by
      rw [List.prod_cons] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact List.mem_cons.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hl q (by simp))).mp h))
      · exact List.mem_cons_of_mem _
          (mem_of_prime_dvd_prod hp l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) h)

section Field

variable {k : Type} [Field k]

@[expose] def rot2 {c s : k} (h : c ^ 2 + s ^ 2 = 1) : SL(2, k) :=
  ⟨!![c, -s; s, c], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem coe_rot2 {c s : k} (h : c ^ 2 + s ^ 2 = 1) :
    ((rot2 h : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![c, -s; s, c] :=
  rfl

@[expose] def delta2 {ω : k} (hω : ω ^ 2 + ω + 1 = 0) : SL(2, k) :=
  ⟨!![ω, 0; 0, ω ^ 2], by rw [Matrix.det_fin_two_of]; linear_combination (ω - 1) * hω⟩

theorem coe_delta2 {ω : k} (hω : ω ^ 2 + ω + 1 = 0) :
    ((delta2 hω : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![ω, 0; 0, ω ^ 2] :=
  rfl

@[expose] def z2 {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : k) ≠ 0) : SL(2, k) :=
  ⟨!![-1 / 2, -(1 + 2 * ω) / 2; -(1 + 2 * ω) / 2, -1 / 2], by
    rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination (-4 : k) * hω⟩

theorem coe_z2 {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : k) ≠ 0) :
    ((z2 hω h2 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      !![-1 / 2, -(1 + 2 * ω) / 2; -(1 + 2 * ω) / 2, -1 / 2] :=
  rfl

theorem delta2_pow_three {ω : k} (hω : ω ^ 2 + ω + 1 = 0) : delta2 hω ^ 3 = 1 := by
  ext i j
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  simp only [Matrix.SpecialLinearGroup.coe_pow, coe_delta2, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    grind

theorem delta2_ne_one {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : k) ≠ 0) : delta2 hω ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, k) => (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp [coe_delta2] at this
  apply h3
  rw [this] at hω
  linear_combination hω

theorem trace_delta2_rot2_comm {ω c s : k} (hω : ω ^ 2 + ω + 1 = 0) (h : c ^ 2 + s ^ 2 = 1) :
    ((delta2 hω * rot2 h * (delta2 hω)⁻¹ * (rot2 h)⁻¹ : SL(2, k)) :
      Matrix (Fin 2) (Fin 2) k).trace = 3 * c ^ 2 - 1 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_delta2,
    coe_rot2, Matrix.adjugate_fin_two_of]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  grind

end Field

@[expose] def hessRA : Matrix (Fin 2) (Fin 2) ℤ := !![-7, -24; 24, -7]

@[expose] def hessRB : Matrix (Fin 2) (Fin 2) ℤ := !![-119, -120; 120, -119]

theorem hessRA_pow_one : (hessRA ^ 1) 1 0 = 24 := by decide
theorem hessRA_pow_two : (hessRA ^ 2) 1 0 = -336 := by decide
theorem hessRA_pow_three : (hessRA ^ 3) 1 0 = -10296 := by decide
theorem hessRA_pow_four : (hessRA ^ 4) 1 0 = 354144 := by decide
theorem hessRA_pow_five : (hessRA ^ 5) 1 0 = 1476984 := by decide
theorem hessRB_pow_one : (hessRB ^ 1) 1 0 = 120 := by decide
theorem hessRB_pow_two : (hessRB ^ 2) 1 0 = -28560 := by decide
theorem hessRB_pow_three : (hessRB ^ 3) 1 0 = 3369960 := by decide
theorem hessRB_pow_four : (hessRB ^ 4) 1 0 = 13651680 := by decide
theorem hessRB_pow_five : (hessRB ^ 5) 1 0 = -99498527400 := by decide

section Field

variable {k : Type} [Field k]

theorem twentyfive_ne_zero (h5 : (5 : k) ≠ 0) : (25 : k) ≠ 0 := by
  have : (25 : k) = 5 * 5 := by norm_num
  rw [this]
  exact mul_ne_zero h5 h5

theorem oneSixtyNine_ne_zero (h13 : (13 : k) ≠ 0) : (169 : k) ≠ 0 := by
  have : (169 : k) = 13 * 13 := by norm_num
  rw [this]
  exact mul_ne_zero h13 h13

theorem rotA_sq (h5 : (5 : k) ≠ 0) : (-7 / 25 : k) ^ 2 + (24 / 25) ^ 2 = 1 := by
  have h25 := twentyfive_ne_zero h5
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 h25)]
  norm_num

theorem rotB_sq (h13 : (13 : k) ≠ 0) : (-119 / 169 : k) ^ 2 + (120 / 169) ^ 2 = 1 := by
  have h169 := oneSixtyNine_ne_zero h13
  rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 h169)]
  norm_num

theorem coe_rot2_eq_smul {c s : k} (h : c ^ 2 + s ^ 2 = 1) {N : ℤ} (hN : (N : k) ≠ 0)
    {R : Matrix (Fin 2) (Fin 2) ℤ} (hR : R.map (Int.cast : ℤ → k) = (N : k) • !![c, -s; s, c]) :
    ((rot2 h : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = (N : k)⁻¹ • R.map (Int.cast : ℤ → k) := by
  rw [hR, smul_smul, inv_mul_cancel₀ hN, one_smul, coe_rot2]

theorem rot2_pow_entry {c s : k} (h : c ^ 2 + s ^ 2 = 1) {N : ℤ} (hN : (N : k) ≠ 0)
    {R : Matrix (Fin 2) (Fin 2) ℤ} (hR : R.map (Int.cast : ℤ → k) = (N : k) • !![c, -s; s, c])
    {j : ℕ} (hj : rot2 h ^ j = 1 ∨ rot2 h ^ j = -1) : (((R ^ j) 1 0 : ℤ) : k) = 0 := by
  have hval : ((rot2 h ^ j : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      (N : k)⁻¹ ^ j • (R ^ j).map (Int.cast : ℤ → k) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_rot2_eq_smul h hN hR, smul_pow]
    congr 1
    exact (map_pow (Int.castRingHom k).mapMatrix R j).symm
  have h10 : ((rot2 h ^ j : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rcases hj with hj | hj <;> rw [hj] <;> simp
  rw [hval] at h10
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h10
  exact (mul_eq_zero.mp h10).resolve_left (pow_ne_zero _ (inv_ne_zero hN))

@[expose] def rotA (h5 : (5 : k) ≠ 0) : SL(2, k) := rot2 (rotA_sq h5)

@[expose] def rotB (h13 : (13 : k) ≠ 0) : SL(2, k) := rot2 (rotB_sq h13)

theorem hessRA_map (h5 : (5 : k) ≠ 0) :
    hessRA.map (Int.cast : ℤ → k) =
      ((25 : ℤ) : k) • !![(-7 / 25 : k), -(24 / 25); 24 / 25, -7 / 25] := by
  have h25 := twentyfive_ne_zero h5
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessRA] <;> field_simp

theorem hessRB_map (h13 : (13 : k) ≠ 0) :
    hessRB.map (Int.cast : ℤ → k) =
      ((169 : ℤ) : k) • !![(-119 / 169 : k), -(120 / 169); 120 / 169, -119 / 169] := by
  have h169 := oneSixtyNine_ne_zero h13
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessRB] <;> field_simp

end Field

section CharP

variable {k : Type} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

theorem natCast_ne_zero_of' {n : ℕ} (h : ¬ p ∣ n) : (n : k) ≠ 0 := by
  intro h0
  exact h ((CharP.cast_eq_zero_iff k p n).mp h0)

theorem prime_ne_zero_of {q : ℕ} (hq : q.Prime) (hpq : p ≠ q) : (q : k) ≠ 0 :=
  natCast_ne_zero_of' (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp h))

theorem mem_of_intCast_eq_zero {n : ℤ} (h : (n : k) = 0) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime)
    (hn : n.natAbs = l.prod) : p ∈ l := by
  have hdvd := (CharP.intCast_eq_zero_iff k p n).mp h
  have : p ∣ n.natAbs := Int.natCast_dvd.mp hdvd
  rw [hn] at this
  exact mem_of_prime_dvd_prod hp.out l hl this

theorem rotA_pow_ne (h5 : (5 : k) ≠ 0)
    (hbad : p ∉ ([2, 3, 7, 11, 13, 17, 19, 31, 41, 79] : List ℕ)) {j : ℕ} (hj1 : 1 ≤ j)
    (hj5 : j ≤ 5) : rotA h5 ^ j ≠ 1 ∧ rotA h5 ^ j ≠ -1 := by
  have h25 : ((25 : ℤ) : k) ≠ 0 := by exact_mod_cast twentyfive_ne_zero h5
  have key : ∀ hj : rotA h5 ^ j = 1 ∨ rotA h5 ^ j = -1, False := by
    intro hj
    have h0 := rot2_pow_entry (rotA_sq h5) h25 (hessRA_map h5) hj
    apply hbad
    interval_cases j
    · rw [hessRA_pow_one] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 3] (by norm_num) (by norm_num)
      simp at this ⊢; omega
    · rw [hessRA_pow_two] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 2, 3, 7] (by norm_num) (by norm_num)
      simp at this ⊢; omega
    · rw [hessRA_pow_three] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 3, 3, 11, 13] (by norm_num) (by norm_num)
      simp at this ⊢; omega
    · rw [hessRA_pow_four] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 2, 2, 3, 7, 17, 31] (by norm_num) (by norm_num)
      simp at this ⊢; omega
    · rw [hessRA_pow_five] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 3, 19, 41, 79] (by norm_num) (by norm_num)
      simp at this ⊢; omega
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem rotB_pow_ne (h13 : (13 : k) ≠ 0)
    (hbad : p ∉ ([2, 3, 5, 7, 11, 17, 19, 23, 37, 61, 199, 239, 719] : List ℕ)) {j : ℕ}
    (hj1 : 1 ≤ j) (hj5 : j ≤ 5) : rotB h13 ^ j ≠ 1 ∧ rotB h13 ^ j ≠ -1 := by
  have h169 : ((169 : ℤ) : k) ≠ 0 := by exact_mod_cast oneSixtyNine_ne_zero h13
  have key : ∀ hj : rotB h13 ^ j = 1 ∨ rotB h13 ^ j = -1, False := by
    intro hj
    have h0 := rot2_pow_entry (rotB_sq h13) h169 (hessRB_map h13) hj
    apply hbad
    interval_cases j
    · rw [hessRB_pow_one] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 3, 5] (by norm_num) (by norm_num)
      simp at this ⊢; omega
    · rw [hessRB_pow_two] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 2, 3, 5, 7, 17] (by norm_num) (by norm_num)
      simp at this ⊢; omega
    · rw [hessRB_pow_three] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 3, 3, 5, 11, 23, 37] (by norm_num)
        (by norm_num)
      simp at this ⊢; omega
    · rw [hessRB_pow_four] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 2, 2, 3, 5, 7, 17, 239] (by norm_num)
        (by norm_num)
      simp at this ⊢; omega
    · rw [hessRB_pow_five] at h0
      have := mem_of_intCast_eq_zero h0 [2, 2, 2, 3, 5, 5, 19, 61, 199, 719] (by norm_num)
        (by norm_num)
      simp at this ⊢; omega
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem rotA_trace_ne {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (h5 : (5 : k) ≠ 0)
    (hbad : p ∉ ([2, 3, 193] : List ℕ)) :
    ((delta2 hω * rotA h5 * (delta2 hω)⁻¹ * (rotA h5)⁻¹ : SL(2, k)) :
        Matrix (Fin 2) (Fin 2) k).trace ≠ 2 ∧
      ((delta2 hω * rotA h5 * (delta2 hω)⁻¹ * (rotA h5)⁻¹ : SL(2, k)) :
        Matrix (Fin 2) (Fin 2) k).trace ≠ -2 := by
  have h25 := twentyfive_ne_zero h5
  rw [rotA, trace_delta2_rot2_comm]
  constructor
  · intro h
    have h0 : ((1728 : ℤ) : k) = 0 := by
      field_simp at h
      push_cast
      linear_combination -h
    apply hbad
    have := mem_of_intCast_eq_zero h0 [2, 2, 2, 2, 2, 2, 3, 3, 3] (by norm_num) (by norm_num)
    simp at this ⊢; omega
  · intro h
    have h0 : ((772 : ℤ) : k) = 0 := by
      field_simp at h
      push_cast
      linear_combination h
    apply hbad
    have := mem_of_intCast_eq_zero h0 [2, 2, 193] (by norm_num) (by norm_num)
    simp at this ⊢; omega

theorem rotB_trace_ne {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (h13 : (13 : k) ≠ 0)
    (hbad : p ∉ ([2, 3, 5, 17761] : List ℕ)) :
    ((delta2 hω * rotB h13 * (delta2 hω)⁻¹ * (rotB h13)⁻¹ : SL(2, k)) :
        Matrix (Fin 2) (Fin 2) k).trace ≠ 2 ∧
      ((delta2 hω * rotB h13 * (delta2 hω)⁻¹ * (rotB h13)⁻¹ : SL(2, k)) :
        Matrix (Fin 2) (Fin 2) k).trace ≠ -2 := by
  have h169 := oneSixtyNine_ne_zero h13
  rw [rotB, trace_delta2_rot2_comm]
  constructor
  · intro h
    have h0 : ((43200 : ℤ) : k) = 0 := by
      field_simp at h
      push_cast
      linear_combination -h
    apply hbad
    have := mem_of_intCast_eq_zero h0 [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5] (by norm_num)
      (by norm_num)
    simp at this ⊢; omega
  · intro h
    have h0 : ((71044 : ℤ) : k) = 0 := by
      field_simp at h
      push_cast
      linear_combination h
    apply hbad
    have := mem_of_intCast_eq_zero h0 [2, 2, 17761] (by norm_num) (by norm_num)
    simp at this ⊢; omega

end CharP

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
