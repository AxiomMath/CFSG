module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CFSG.RankThree.SubgroupLists2.SpectralBounds
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType.KG87B

open Matrix

variable {Ω : Type*} [Field Ω]

@[expose] def heisX (ω : Ω) : Matrix (Fin 6) (Fin 6) Ω := diagonal ![1, 1, ω, ω, ω ^ 2, ω ^ 2]

@[expose] def heisY : Matrix (Fin 6) (Fin 6) Ω := of fun i j => if i = j + 2 then 1 else 0

@[expose] def heisD (l m : Ω) : Matrix (Fin 6) (Fin 6) Ω := diagonal ![l, m, l, m, l, m]

private theorem mul_heisY_apply (M : Matrix (Fin 6) (Fin 6) Ω) (k l : Fin 6) :
    (M * heisY : Matrix (Fin 6) (Fin 6) Ω) k l = M k (l + 2) := by
  simp [heisY, Matrix.mul_apply]

private theorem heisY_mul_apply (M : Matrix (Fin 6) (Fin 6) Ω) (k l : Fin 6) :
    (heisY * M : Matrix (Fin 6) (Fin 6) Ω) k l = M (k + 4) l := by
  have h24 : (2 : Fin 6) + 4 = 0 := by decide
  have h42 : (4 : Fin 6) + 2 = 0 := by decide
  simp only [heisY, Matrix.mul_apply, of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (k + 4)
    (fun b _ hb => if_neg fun h => hb (by rw [h, add_assoc, h24, add_zero])) (by simp),
    if_pos (by rw [add_assoc, h42, add_zero])]

theorem heisX_mul_heisY {ω : Ω} (hω : ω ^ 3 = 1) : heisX ω * heisY = ω • (heisY * heisX ω) := by
  ext k l
  rw [Matrix.smul_apply, mul_heisY_apply, heisY_mul_apply, smul_eq_mul]
  fin_cases k <;> fin_cases l <;> simp [heisX, ← pow_succ', hω] <;> ring

theorem heisY_mul_heisX {ω : Ω} (hω : ω ^ 3 = 1) : heisY * heisX ω = ω ^ 2 • (heisX ω * heisY) := by
  rw [heisX_mul_heisY hω, smul_smul, show ω ^ 2 * ω = 1 by linear_combination hω, one_smul]

theorem heisX_pow_three {ω : Ω} (hω : ω ^ 3 = 1) : heisX ω ^ 3 = 1 := by
  rw [heisX, diagonal_pow, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp [hω, ← pow_mul] <;> linear_combination (ω ^ 3 + 1) * hω

theorem heisY_pow_three : (heisY : Matrix (Fin 6) (Fin 6) Ω) ^ 3 = 1 := by
  ext k l
  rw [pow_succ, mul_heisY_apply, pow_two, mul_heisY_apply]
  fin_cases k <;> fin_cases l <;> simp [heisY, one_apply]

private theorem heisY_pow_pow_three (n : ℕ) : ((heisY : Matrix (Fin 6) (Fin 6) Ω) ^ n) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, heisY_pow_three, one_pow]

private theorem heisX_pow_pow_three {ω : Ω} (hω : ω ^ 3 = 1) (n : ℕ) : (heisX ω ^ n) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, heisX_pow_three hω, one_pow]

section Twisted

variable {R : Type*} [Ring R] [Algebra Ω R]

private theorem mul_pow_eq_smul {a b : R} {c : Ω} (h : a * b = c • (b * a)) (n : ℕ) :
    a * b ^ n = c ^ n • (b ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc a * b ^ (n + 1) = a * b ^ n * b := by rw [pow_succ, mul_assoc]
      _ = c ^ n • (b ^ n * (a * b)) := by rw [ih, smul_mul_assoc, mul_assoc]
      _ = c ^ (n + 1) • (b ^ (n + 1) * a) := by
        rw [h, mul_smul_comm, smul_smul, ← mul_assoc, ← pow_succ, ← pow_succ]

private theorem pow_mul_eq_smul {a b : R} {c : Ω} (h : a * b = c • (b * a)) (n : ℕ) :
    a ^ n * b = c ^ n • (b * a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc a ^ (n + 1) * b = a * (a ^ n * b) := by rw [pow_succ', mul_assoc]
      _ = c ^ n • (a * b * a ^ n) := by rw [ih, mul_smul_comm, mul_assoc]
      _ = c ^ (n + 1) • (b * a ^ (n + 1)) := by
        rw [h, smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ', ← pow_succ]

private def CR3 (a b : R) : Prop := ∃ c : Ω, c ^ 3 = 1 ∧ a * b = c • (b * a)

private theorem CR3.symm {a b : R} (h : CR3 (Ω := Ω) a b) : CR3 (Ω := Ω) b a := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hc, one_pow], ?_⟩
  rw [h, smul_smul, ← pow_succ, hc, one_smul]

private theorem CR3.refl (a : R) : CR3 (Ω := Ω) a a := ⟨1, one_pow 3, by rw [one_smul]⟩

private theorem CR3.one_left (a : R) : CR3 (Ω := Ω) 1 a :=
  ⟨1, one_pow 3, by rw [one_mul, mul_one, one_smul]⟩

private theorem CR3.mul_left {a b d : R} (h₁ : CR3 (Ω := Ω) a d) (h₂ : CR3 (Ω := Ω) b d) :
    CR3 (Ω := Ω) (a * b) d := by
  obtain ⟨c₁, hc₁, h₁⟩ := h₁
  obtain ⟨c₂, hc₂, h₂⟩ := h₂
  refine ⟨c₁ * c₂, by rw [mul_pow, hc₁, hc₂, one_mul], ?_⟩
  calc a * b * d = c₂ • (a * d * b) := by rw [mul_assoc, h₂, mul_smul_comm, ← mul_assoc]
    _ = (c₁ * c₂) • (d * (a * b)) := by
      rw [h₁, smul_mul_assoc, smul_smul, mul_comm c₂, mul_assoc]

private theorem CR3.mul_right {a b d : R} (h₁ : CR3 (Ω := Ω) d a) (h₂ : CR3 (Ω := Ω) d b) :
    CR3 (Ω := Ω) d (a * b) :=
  (h₁.symm.mul_left h₂.symm).symm

private theorem CR3.pow_left {a d : R} (h : CR3 (Ω := Ω) a d) (n : ℕ) :
    CR3 (Ω := Ω) (a ^ n) d := by
  induction n with
  | zero => rw [pow_zero]; exact CR3.one_left d
  | succ n ih => rw [pow_succ]; exact ih.mul_left h

private theorem CR3.pow_right {a d : R} (h : CR3 (Ω := Ω) d a) (n : ℕ) :
    CR3 (Ω := Ω) d (a ^ n) :=
  (h.symm.pow_left n).symm

private theorem CR3.mul_pow_three {a b : R} (h : CR3 (Ω := Ω) a b) :
    (a * b) ^ 3 = a ^ 3 * b ^ 3 := by
  obtain ⟨c, hc, h⟩ := h.symm
  have h' : ∀ x, b * (a * x) = c • (a * (b * x)) := fun x => by
    rw [← mul_assoc, h, smul_mul_assoc, mul_assoc]
  have hc' : c * (c * c) = 1 := by linear_combination hc
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, h', mul_smul_comm, smul_mul_assoc, smul_smul,
    hc', one_smul]

end Twisted

private theorem omega_ne_sq {ω : Ω} (h3 : (3 : Ω) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ ω ^ 2 :=
  fun h => h3 (by linear_combination (3 - 2 * ω) * hω - (2 * ω + 1) * h)

section Block

private def blk (N : Matrix (Fin 2) (Fin 2) Ω) : Matrix (Fin 6) (Fin 6) Ω :=
  !![N 0 0, N 0 1, 0, 0, 0, 0;
     N 1 0, N 1 1, 0, 0, 0, 0;
     0, 0, N 0 0, N 0 1, 0, 0;
     0, 0, N 1 0, N 1 1, 0, 0;
     0, 0, 0, 0, N 0 0, N 0 1;
     0, 0, 0, 0, N 1 0, N 1 1]

private theorem blk_mul (N N' : Matrix (Fin 2) (Fin 2) Ω) : blk N * blk N' = blk (N * N') := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_two]

private theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) Ω) = 1 := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [blk, one_apply]

private theorem blk_smul (c : Ω) (N : Matrix (Fin 2) (Fin 2) Ω) : blk (c • N) = c • blk N := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [blk]

private theorem blk_pow (N : Matrix (Fin 2) (Fin 2) Ω) (n : ℕ) : blk N ^ n = blk (N ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blk_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, blk_mul]

private theorem blk_injective {N N' : Matrix (Fin 2) (Fin 2) Ω} (h : blk N = blk N') : N = N' := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [blk] using congrFun (congrFun h 0) 0
  · simpa [blk] using congrFun (congrFun h 0) 1
  · simpa [blk] using congrFun (congrFun h 1) 0
  · simpa [blk] using congrFun (congrFun h 1) 1

private theorem blk_mul_heisX (N : Matrix (Fin 2) (Fin 2) Ω) (ω : Ω) :
    blk N * heisX ω = heisX ω * blk N := by
  ext k l
  rw [heisX, mul_diagonal, diagonal_mul]
  fin_cases k <;> fin_cases l <;> simp [blk, mul_comm]

private theorem blk_mul_heisY (N : Matrix (Fin 2) (Fin 2) Ω) : blk N * heisY = heisY * blk N := by
  ext k l
  rw [mul_heisY_apply, heisY_mul_apply]
  fin_cases k <;> fin_cases l <;> simp [blk]

private theorem blk_diagonal (e : Fin 2 → Ω) : blk (diagonal e) = heisD (e 0) (e 1) := by
  ext k l
  fin_cases k <;> fin_cases l <;> simp [blk, heisD]

private theorem exists_blk_of_comm {ω : Ω} (h3 : (3 : Ω) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0)
    {D : Matrix (Fin 6) (Fin 6) Ω} (hX : D * heisX ω = heisX ω * D) (hY : D * heisY = heisY * D) :
    ∃ N : Matrix (Fin 2) (Fin 2) Ω, D = blk N := by
  have n01 : (1 : Ω) ≠ ω := fun h => h3 (by rw [← h] at hω; linear_combination hω)
  have n02 : (1 : Ω) ≠ ω ^ 2 := fun h => h3 (by linear_combination (1 - ω) * h + (2 - ω) * hω)
  have n12 : ω ≠ ω ^ 2 := omega_ne_sq h3 hω
  have hz : ∀ k l, (![1, 1, ω, ω, ω ^ 2, ω ^ 2] : Fin 6 → Ω) k ≠ ![1, 1, ω, ω, ω ^ 2, ω ^ 2] l →
      D k l = 0 := by
    intro k l hkl
    have := congrFun (congrFun hX k) l
    rw [heisX, mul_diagonal, diagonal_mul] at this
    by_contra hD
    exact hkl (mul_left_cancel₀ hD (by rw [this, mul_comm])).symm
  have he : ∀ k l : Fin 6, D (k + 2) (l + 2) = D k l := by
    intro k l
    have := congrFun (congrFun hY (k + 2)) l
    rw [mul_heisY_apply, heisY_mul_apply] at this
    rw [this, add_assoc, show (2 : Fin 6) + 4 = 0 by decide, add_zero]
  have e22 : D 2 2 = D 0 0 := by simpa using he 0 0
  have e23 : D 2 3 = D 0 1 := by simpa using he 0 1
  have e32 : D 3 2 = D 1 0 := by simpa using he 1 0
  have e33 : D 3 3 = D 1 1 := by simpa using he 1 1
  have e44 : D 4 4 = D 0 0 := by simpa [e22] using he 2 2
  have e45 : D 4 5 = D 0 1 := by simpa [e23] using he 2 3
  have e54 : D 5 4 = D 1 0 := by simpa [e32] using he 3 2
  have e55 : D 5 5 = D 1 1 := by simpa [e33] using he 3 3
  refine ⟨!![D 0 0, D 0 1; D 1 0, D 1 1], ?_⟩
  ext k l
  fin_cases k <;> fin_cases l <;> simp [blk, e22, e23, e32, e33, e44, e45, e54, e55] <;>
    exact hz _ _ (by simp [n01, n02, n12, n01.symm, n02.symm, n12.symm])

end Block

section Basis

private theorem eq_zero_of_eigen_sum {ω : Ω} (h3 : (3 : Ω) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0)
    {X : Matrix (Fin 6) (Fin 6) Ω} {v₀ v₁ v₂ : Fin 6 → Ω} (h₀ : X *ᵥ v₀ = v₀)
    (h₁ : X *ᵥ v₁ = ω • v₁) (h₂ : X *ᵥ v₂ = ω ^ 2 • v₂) (h : v₀ + v₁ + v₂ = 0) :
    v₀ = 0 ∧ v₁ = 0 ∧ v₂ = 0 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have e1 : v₀ + ω • v₁ + ω ^ 2 • v₂ = 0 := by
    have := congrArg (X *ᵥ ·) h
    simpa only [mulVec_add, h₀, h₁, h₂, mulVec_zero] using this
  have e2 : v₀ + ω ^ 2 • v₁ + ω • v₂ = 0 := by
    have := congrArg (X *ᵥ ·) e1
    simp only [mulVec_add, mulVec_smul, h₀, h₁, h₂, mulVec_zero, smul_smul] at this
    rwa [show ω * ω = ω ^ 2 by ring, show ω ^ 2 * ω ^ 2 = ω by linear_combination ω * hω3] at this
  have hne := sub_ne_zero.2 (omega_ne_sq h3 hω)
  have hk : ∀ k, v₀ k = 0 ∧ v₁ k = 0 ∧ v₂ k = 0 := by
    intro k
    have a := congrFun h k
    have b := congrFun e1 k
    have c := congrFun e2 k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a b c
    have hv₀ : v₀ k = 0 := by
      have : (3 : Ω) * v₀ k = 0 := by linear_combination a + b + c - (v₁ k + v₂ k) * hω
      exact (mul_eq_zero.1 this).resolve_left h3
    have hv₁ : v₁ k = 0 := by
      have : (ω - ω ^ 2) * v₁ k = 0 := by linear_combination b - ω ^ 2 * a - (1 - ω ^ 2) * hv₀
      exact (mul_eq_zero.1 this).resolve_left hne
    exact ⟨hv₀, hv₁, by linear_combination a - hv₀ - hv₁⟩
  exact ⟨funext fun k => (hk k).1, funext fun k => (hk k).2.1, funext fun k => (hk k).2.2⟩

private theorem exists_heis_basis {ω : Ω} (h3 : (3 : Ω) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0)
    {X Y : Matrix (Fin 6) (Fin 6) Ω} (hX : X ^ 3 = 1) (hY : Y ^ 3 = 1)
    (hXY : X * Y = ω • (Y * X)) :
    ∃ P : Matrix (Fin 6) (Fin 6) Ω, IsUnit P ∧ X * P = P * heisX ω ∧ Y * P = P * heisY := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hXY2 : X * Y ^ 2 = ω ^ 2 • (Y ^ 2 * X) := mul_pow_eq_smul hXY 2
  have hYY2 : Y * Y ^ 2 = 1 := by rw [← pow_succ', hY]
  have hY2Y : Y ^ 2 * Y = 1 := by rw [← pow_succ, hY]
  have hXX2 : X * X ^ 2 = 1 := by rw [← pow_succ', hX]
  have hXYv : ∀ v, X *ᵥ v = v → X *ᵥ (Y *ᵥ v) = ω • (Y *ᵥ v) := fun v hv => by
    rw [mulVec_mulVec, hXY, smul_mulVec, ← mulVec_mulVec, hv]
  have hXY2v : ∀ v, X *ᵥ v = v → X *ᵥ (Y ^ 2 *ᵥ v) = ω ^ 2 • (Y ^ 2 *ᵥ v) := fun v hv => by
    rw [mulVec_mulVec, hXY2, smul_mulVec, ← mulVec_mulVec, hv]
  let W : Submodule Ω (Fin 6 → Ω) := LinearMap.ker (X - 1).mulVecLin
  have hmemW : ∀ v, v ∈ W ↔ X *ᵥ v = v := fun v => by
    simp only [W, LinearMap.mem_ker, mulVecLin_apply, sub_mulVec, one_mulVec, sub_eq_zero]
  let π₀ : Matrix (Fin 6) (Fin 6) Ω := (3 : Ω)⁻¹ • (1 + X + X ^ 2)
  let π₁ : Matrix (Fin 6) (Fin 6) Ω := (3 : Ω)⁻¹ • (1 + ω ^ 2 • X + ω • X ^ 2)
  let π₂ : Matrix (Fin 6) (Fin 6) Ω := (3 : Ω)⁻¹ • (1 + ω • X + ω ^ 2 • X ^ 2)
  have hsum : π₀ + π₁ + π₂ = 1 := by
    simp only [π₀, π₁, π₂, ← smul_add]
    rw [show (1 + X + X ^ 2) + (1 + ω ^ 2 • X + ω • X ^ 2) + (1 + ω • X + ω ^ 2 • X ^ 2) =
        (3 : Ω) • (1 : Matrix (Fin 6) (Fin 6) Ω) + (ω ^ 2 + ω + 1) • X + (ω ^ 2 + ω + 1) • X ^ 2 by
      module, hω, zero_smul, zero_smul, add_zero, add_zero, smul_smul, inv_mul_cancel₀ h3,
      one_smul]
  have hπ₀ : X * π₀ = π₀ := by
    simp only [π₀, mul_smul_comm, mul_add, mul_one, hXX2, ← sq]
    congr 1
    abel
  have hπ₁ : X * π₁ = ω • π₁ := by
    simp only [π₁, mul_smul_comm, mul_add, mul_one, hXX2, ← sq, smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination (-(3 : Ω)⁻¹) * hω3
  have hπ₂ : X * π₂ = ω ^ 2 • π₂ := by
    simp only [π₂, mul_smul_comm, mul_add, mul_one, hXX2, ← sq, smul_add, smul_smul]
    match_scalars <;> first | ring1 | linear_combination (-(3 : Ω)⁻¹) * hω3 |
      linear_combination (-(3 : Ω)⁻¹ * ω) * hω3
  have htop : (⊤ : Submodule Ω (Fin 6 → Ω)) ≤
      W ⊔ W.map Y.mulVecLin ⊔ W.map (Y ^ 2).mulVecLin := by
    intro v _
    have hv : v = π₀ *ᵥ v + Y *ᵥ ((Y ^ 2 * π₁) *ᵥ v) + Y ^ 2 *ᵥ ((Y * π₂) *ᵥ v) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← mul_assoc, ← mul_assoc, hYY2, hY2Y, one_mul, one_mul,
        ← add_mulVec, ← add_mulVec, hsum, one_mulVec]
    have h0 : π₀ *ᵥ v ∈ W := (hmemW _).2 (by rw [mulVec_mulVec, hπ₀])
    have h1 : (Y ^ 2 * π₁) *ᵥ v ∈ W := (hmemW _).2 (by
      rw [mulVec_mulVec, ← mul_assoc, hXY2, smul_mul_assoc, mul_assoc, hπ₁, mul_smul_comm,
        smul_smul, show ω ^ 2 * ω = 1 by linear_combination hω3, one_smul])
    have h2 : (Y * π₂) *ᵥ v ∈ W := (hmemW _).2 (by
      rw [mulVec_mulVec, ← mul_assoc, hXY, smul_mul_assoc, mul_assoc, hπ₂, mul_smul_comm,
        smul_smul, show ω * ω ^ 2 = 1 by linear_combination hω3, one_smul])
    rw [hv]
    exact add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left h0))
      (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem h1))))
      (Submodule.mem_sup_right (Submodule.mem_map_of_mem h2))
  have hdim : 2 ≤ Module.finrank Ω W := by
    have h1 := Submodule.finrank_mono htop
    rw [finrank_top, Module.finrank_fin_fun] at h1
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (W ⊔ W.map Y.mulVecLin)
      (W.map (Y ^ 2).mulVecLin)
    have h3' := Submodule.finrank_add_le_finrank_add_finrank W (W.map Y.mulVecLin)
    have h4 := Submodule.finrank_map_le Y.mulVecLin W
    have h5 := Submodule.finrank_map_le (Y ^ 2).mulVecLin W
    omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hdim
  set w₀ : Fin 6 → Ω := (f 0 : Fin 6 → Ω)
  set w₁ : Fin 6 → Ω := (f 1 : Fin 6 → Ω)
  have hw₀ : X *ᵥ w₀ = w₀ := (hmemW _).1 (f 0).2
  have hw₁ : X *ᵥ w₁ = w₁ := (hmemW _).1 (f 1).2
  have hli : ∀ s t : Ω, s • w₀ + t • w₁ = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have := Fintype.linearIndependent_iff.1 hf ![s, t] (by
      rw [Fin.sum_univ_two]
      exact Submodule.coe_eq_zero.1 (by simpa using hst))
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  let col : Fin 6 → Fin 6 → Ω := ![w₀, w₁, Y *ᵥ w₀, Y *ᵥ w₁, Y ^ 2 *ᵥ w₀, Y ^ 2 *ᵥ w₁]
  let P : Matrix (Fin 6) (Fin 6) Ω := of fun i j => col j i
  have hmulP : ∀ (A : Matrix (Fin 6) (Fin 6) Ω) k j, (A * P) k j = (A *ᵥ col j) k := by
    intro A k j
    simp [P, Matrix.mul_apply, mulVec, dotProduct]
  have hXcol : ∀ j, X *ᵥ col j = (![1, 1, ω, ω, ω ^ 2, ω ^ 2] : Fin 6 → Ω) j • col j := by
    intro j
    fin_cases j <;> simp [col, hw₀, hw₁, hXYv _ hw₀, hXYv _ hw₁, hXY2v _ hw₀, hXY2v _ hw₁]
  have hYcol : ∀ j, Y *ᵥ col j = col (j + 2) := by
    intro j
    fin_cases j <;> simp [col, mulVec_mulVec, ← sq, hYY2]
  have hXP : X * P = P * heisX ω := by
    ext k j
    rw [hmulP, heisX, mul_diagonal, hXcol]
    simp [P, mul_comm]
  have hYP : Y * P = P * heisY := by
    ext k j
    rw [hmulP, mul_heisY_apply, hYcol]
    rfl
  refine ⟨P, ?_, hXP, hYP⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hc0
  have hPc : P *ᵥ c = ∑ j, c j • col j := by
    ext k
    simp [P, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hPc, Fin.sum_univ_six] at hc
  have hfix : ∀ s t : Ω, X *ᵥ (s • w₀ + t • w₁) = s • w₀ + t • w₁ := fun s t => by
    rw [mulVec_add, mulVec_smul, mulVec_smul, hw₀, hw₁]
  have hsum' : (c 0 • w₀ + c 1 • w₁) + Y *ᵥ (c 2 • w₀ + c 3 • w₁) +
      Y ^ 2 *ᵥ (c 4 • w₀ + c 5 • w₁) = 0 := by
    simp only [mulVec_add, mulVec_smul]
    rw [← hc]
    simp only [col, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    abel
  obtain ⟨e0, e1, e2⟩ := eq_zero_of_eigen_sum h3 hω (hfix _ _) (hXYv _ (hfix _ _))
    (hXY2v _ (hfix _ _)) hsum'
  have e1' : c 2 • w₀ + c 3 • w₁ = 0 := by
    rw [← one_mulVec (c 2 • w₀ + c 3 • w₁), ← hY2Y, ← mulVec_mulVec, e1, mulVec_zero]
  have e2' : c 4 • w₀ + c 5 • w₁ = 0 := by
    rw [← one_mulVec (c 4 • w₀ + c 5 • w₁), ← hYY2, ← mulVec_mulVec, e2, mulVec_zero]
  obtain ⟨c0, c1⟩ := hli _ _ e0
  obtain ⟨c2, c3⟩ := hli _ _ e1'
  obtain ⟨c4, c5⟩ := hli _ _ e2'
  funext j
  fin_cases j
  exacts [c0, c1, c2, c3, c4, c5]

end Basis

section Normal

private theorem cube_root_cases {ω c : Ω} (hω : ω ^ 2 + ω + 1 = 0) (hc : c ^ 3 = 1) :
    c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  have h : (c - 1) * (c - ω) * (c - ω ^ 2) = 0 := by
    linear_combination hc + (c - 1) * (ω - 1 - c) * hω
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h))

private theorem exists_twist_two {ω β : Ω} (hω : ω ^ 2 + ω + 1 = 0) (hβ : β ^ 3 = 1) :
    ∃ i < 3, β * ω ^ (2 * i) = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  rcases cube_root_cases hω hβ with h | h | h <;> rw [h]
  · exact ⟨0, by norm_num, by ring⟩
  · exact ⟨1, by norm_num, by linear_combination hω3⟩
  · exact ⟨2, by norm_num, by linear_combination (ω ^ 3 + 1) * hω3⟩

private theorem exists_twist_four {ω α : Ω} (hω : ω ^ 2 + ω + 1 = 0) (hα : α ^ 3 = 1) :
    ∃ j < 3, α * ω ^ (4 * j) = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  rcases cube_root_cases hω hα with h | h | h <;> rw [h]
  · exact ⟨0, by norm_num, by ring⟩
  · exact ⟨2, by norm_num, by linear_combination (ω ^ 6 + ω ^ 3 + 1) * hω3⟩
  · exact ⟨1, by norm_num, by linear_combination (ω ^ 3 + 1) * hω3⟩

private theorem twist_comm {ω α β : Ω} (hω3 : ω ^ 3 = 1) {M : Matrix (Fin 6) (Fin 6) Ω} {i j : ℕ}
    (hα : M * heisX ω = α • (heisX ω * M)) (hβ : M * heisY = β • (heisY * M))
    (hαj : α * ω ^ (4 * j) = 1) (hβi : β * ω ^ (2 * i) = 1) :
    heisY ^ (2 * j) * heisX ω ^ (2 * i) * M * heisX ω =
        heisX ω * (heisY ^ (2 * j) * heisX ω ^ (2 * i) * M) ∧
      heisY ^ (2 * j) * heisX ω ^ (2 * i) * M * heisY =
        heisY * (heisY ^ (2 * j) * heisX ω ^ (2 * i) * M) := by
  set X₀ := heisX ω
  set Y₀ : Matrix (Fin 6) (Fin 6) Ω := heisY
  have hXY : X₀ * Y₀ = ω • (Y₀ * X₀) := heisX_mul_heisY hω3
  have hYX : Y₀ * X₀ = ω ^ 2 • (X₀ * Y₀) := heisY_mul_heisX hω3
  have e2 : Y₀ ^ (2 * j) * X₀ = (ω ^ 2) ^ (2 * j) • (X₀ * Y₀ ^ (2 * j)) := pow_mul_eq_smul hYX _
  have e3 : X₀ ^ (2 * i) * Y₀ = ω ^ (2 * i) • (Y₀ * X₀ ^ (2 * i)) := pow_mul_eq_smul hXY _
  constructor
  · calc Y₀ ^ (2 * j) * X₀ ^ (2 * i) * M * X₀
        = α • (Y₀ ^ (2 * j) * (X₀ ^ (2 * i) * X₀) * M) := by
          rw [mul_assoc _ M, hα, mul_smul_comm]
          simp only [mul_assoc]
      _ = α • ((Y₀ ^ (2 * j) * X₀) * X₀ ^ (2 * i) * M) := by
          rw [pow_mul_comm']
          simp only [mul_assoc]
      _ = (α * (ω ^ 2) ^ (2 * j)) • (X₀ * (Y₀ ^ (2 * j) * X₀ ^ (2 * i) * M)) := by
          rw [e2, smul_mul_assoc, smul_mul_assoc, smul_smul]
          simp only [mul_assoc]
      _ = X₀ * (Y₀ ^ (2 * j) * X₀ ^ (2 * i) * M) := by
          rw [← pow_mul, show 2 * (2 * j) = 4 * j by ring, hαj, one_smul]
  · calc Y₀ ^ (2 * j) * X₀ ^ (2 * i) * M * Y₀
        = β • (Y₀ ^ (2 * j) * (X₀ ^ (2 * i) * Y₀) * M) := by
          rw [mul_assoc _ M, hβ, mul_smul_comm]
          simp only [mul_assoc]
      _ = (β * ω ^ (2 * i)) • ((Y₀ ^ (2 * j) * Y₀) * X₀ ^ (2 * i) * M) := by
          rw [e3, mul_smul_comm, smul_mul_assoc, smul_smul]
          simp only [mul_assoc]
      _ = Y₀ * (Y₀ ^ (2 * j) * X₀ ^ (2 * i) * M) := by
          rw [hβi, one_smul, pow_mul_comm']
          simp only [mul_assoc]

theorem exists_heis_normal_form [IsAlgClosed Ω] (h3 : ((3 : ℕ) : Ω) ≠ 0) {ι : Type*}
    (B : ι → GL (Fin 6) Ω)
    (hcube : ∀ x, ∃ μ : Ω, ((B x ^ 3 : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) = μ • 1)
    (hcomm : ∀ x y, ∃ μ : Ω,
      ((B x * B y * (B x)⁻¹ * (B y)⁻¹ : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) = μ • 1)
    (hnc : ∃ x₁ x₂, B x₁ * B x₂ ≠ B x₂ * B x₁) :
    ∃ (P : GL (Fin 6) Ω) (ω : Ω), ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      ∀ x, ∃ (i j : ℕ) (l m : Ω), i < 3 ∧ j < 3 ∧ l ≠ 0 ∧ m ≠ 0 ∧
        ((P⁻¹ * B x * P : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) =
          heisX ω ^ i * heisY ^ j * heisD l m := by
  have h3' : (3 : Ω) ≠ 0 := by exact_mod_cast h3
  obtain ⟨A, hA⟩ : ∃ A : ι → Matrix (Fin 6) (Fin 6) Ω,
      ∀ x, ((B x : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) = A x := ⟨fun x => B x, fun _ => rfl⟩
  have hA0 : ∀ x, A x ≠ 0 := fun x => hA x ▸ Units.ne_zero (B x)
  have hAcube : ∀ x, ∃ μ : Ω, μ ≠ 0 ∧ A x ^ 3 = μ • 1 := by
    intro x
    obtain ⟨μ, hμ⟩ := hcube x
    have hne : ((B x ^ 3 : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) ≠ 0 := Units.ne_zero _
    rw [hμ] at hne
    rw [Units.val_pow_eq_pow_val, hA] at hμ
    exact ⟨μ, fun h => hne (by rw [h, zero_smul]), hμ⟩
  have hAcomm : ∀ x y, ∃ s : Ω, s ^ 3 = 1 ∧ A x * A y = s • (A y * A x) := by
    intro x y
    obtain ⟨μ, hμ⟩ := hcomm x y
    have e : B x * B y = (B x * B y * (B x)⁻¹ * (B y)⁻¹) * (B y * B x) := by group
    have hxy : A x * A y = μ • (A y * A x) := by
      rw [← hA x, ← hA y, ← Units.val_mul, e, Units.val_mul, hμ, smul_mul_assoc, one_mul,
        Units.val_mul]
    refine ⟨μ, ?_, hxy⟩
    obtain ⟨ν, hν0, hν⟩ := hAcube x
    have h1 := pow_mul_eq_smul hxy 3
    rw [hν, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul] at h1
    have h2 : ν = μ ^ 3 * ν := smul_left_injective Ω (hA0 y) h1
    exact mul_right_cancel₀ hν0 (by rw [one_mul]; exact h2.symm)
  obtain ⟨x₁, x₂, hne⟩ := hnc
  obtain ⟨ω, hω3, h12⟩ := hAcomm x₁ x₂
  have hω1 : ω ≠ 1 := by
    rintro rfl
    exact hne (Units.ext (by rw [Units.val_mul, Units.val_mul, hA, hA, h12, one_smul]))
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  obtain ⟨μ₁, hμ₁0, hμ₁⟩ := hAcube x₁
  obtain ⟨μ₂, hμ₂0, hμ₂⟩ := hAcube x₂
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq μ₁⁻¹ (by norm_num : 0 < 3)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq μ₂⁻¹ (by norm_num : 0 < 3)
  set X := a • A x₁ with hXdef
  set Y := b • A x₂ with hYdef
  have hX : X ^ 3 = 1 := by rw [smul_pow, hμ₁, smul_smul, ha, inv_mul_cancel₀ hμ₁0, one_smul]
  have hY : Y ^ 3 = 1 := by rw [smul_pow, hμ₂, smul_smul, hb, inv_mul_cancel₀ hμ₂0, one_smul]
  have hXY : X * Y = ω • (Y * X) := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, h12, smul_smul, smul_smul, mul_comm a b,
      mul_comm (b * a)]
  obtain ⟨P, hP, hXP, hYP⟩ := exists_heis_basis h3' hω hX hY hXY
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  set cj : Matrix (Fin 6) (Fin 6) Ω → Matrix (Fin 6) (Fin 6) Ω := fun T => P⁻¹ * T * P with hcj
  have cj_mul : ∀ T S, cj (T * S) = cj T * cj S := fun T S => by
    simp only [hcj]
    rw [show P⁻¹ * T * P * (P⁻¹ * S * P) = P⁻¹ * T * (P * P⁻¹) * S * P by
      simp only [mul_assoc], hPP, mul_one]
    simp only [mul_assoc]
  have cj_smul : ∀ (c : Ω) T, cj (c • T) = c • cj T := fun c T => by
    simp only [hcj, mul_smul_comm, smul_mul_assoc]
  have cj_one : cj 1 = 1 := by simp only [hcj, mul_one, hPP']
  have cj_pow : ∀ T (n : ℕ), cj (T ^ n) = cj T ^ n := fun T n => by
    induction n with
    | zero => rw [pow_zero, pow_zero, cj_one]
    | succ n ih => rw [pow_succ, pow_succ, cj_mul, ih]
  have cj_X : cj X = heisX ω := by
    simp only [hcj]
    rw [mul_assoc, hXP, ← mul_assoc, hPP', one_mul]
  have cj_Y : cj Y = heisY := by
    simp only [hcj]
    rw [mul_assoc, hYP, ← mul_assoc, hPP', one_mul]
  have hMX : ∀ x, ∃ α : Ω, α ^ 3 = 1 ∧ cj (A x) * heisX ω = α • (heisX ω * cj (A x)) := by
    intro x
    obtain ⟨α, hα3, hα⟩ := hAcomm x x₁
    refine ⟨α, hα3, ?_⟩
    have : A x * X = α • (X * A x) := by
      rw [hXdef, mul_smul_comm, hα, smul_mul_assoc, smul_comm]
    rw [← cj_X, ← cj_mul, this, cj_smul, cj_mul]
  have hMY : ∀ x, ∃ β : Ω, β ^ 3 = 1 ∧ cj (A x) * heisY = β • (heisY * cj (A x)) := by
    intro x
    obtain ⟨β, hβ3, hβ⟩ := hAcomm x x₂
    refine ⟨β, hβ3, ?_⟩
    have : A x * Y = β • (Y * A x) := by
      rw [hYdef, mul_smul_comm, hβ, smul_mul_assoc, smul_comm]
    rw [← cj_Y, ← cj_mul, this, cj_smul, cj_mul]
  have hMM : ∀ x y, CR3 (Ω := Ω) (cj (A x)) (cj (A y)) := by
    intro x y
    obtain ⟨s, hs3, hs⟩ := hAcomm x y
    exact ⟨s, hs3, by rw [← cj_mul, hs, cj_smul, cj_mul]⟩
  have hMcube : ∀ x, ∃ μ : Ω, μ ≠ 0 ∧ cj (A x) ^ 3 = μ • 1 := by
    intro x
    obtain ⟨μ, hμ0, hμ⟩ := hAcube x
    exact ⟨μ, hμ0, by rw [← cj_pow, hμ, cj_smul, cj_one]⟩
  have hXY0 : CR3 (Ω := Ω) (heisX ω) heisY := ⟨ω, hω3, heisX_mul_heisY hω3⟩
  have hMX' : ∀ x, CR3 (Ω := Ω) (cj (A x)) (heisX ω) := fun x => by
    obtain ⟨α, hα3, hα⟩ := hMX x
    exact ⟨α, hα3, hα⟩
  have hMY' : ∀ x, CR3 (Ω := Ω) (cj (A x)) heisY := fun x => by
    obtain ⟨β, hβ3, hβ⟩ := hMY x
    exact ⟨β, hβ3, hβ⟩
  have hdec : ∀ x, ∃ i j : ℕ, i < 3 ∧ j < 3 ∧
      heisY ^ (2 * j) * heisX ω ^ (2 * i) * cj (A x) * heisX ω =
        heisX ω * (heisY ^ (2 * j) * heisX ω ^ (2 * i) * cj (A x)) ∧
      heisY ^ (2 * j) * heisX ω ^ (2 * i) * cj (A x) * heisY =
        heisY * (heisY ^ (2 * j) * heisX ω ^ (2 * i) * cj (A x)) := by
    intro x
    obtain ⟨α, hα3, hα⟩ := hMX x
    obtain ⟨β, hβ3, hβ⟩ := hMY x
    obtain ⟨j, hj, hαj⟩ := exists_twist_four hω hα3
    obtain ⟨i, hi, hβi⟩ := exists_twist_two hω hβ3
    exact ⟨i, j, hi, hj, twist_comm hω3 hα hβ hαj hβi⟩
  choose i j hi hj hDX hDY using hdec
  set D : ι → Matrix (Fin 6) (Fin 6) Ω :=
    fun x => heisY ^ (2 * j x) * heisX ω ^ (2 * i x) * cj (A x) with hDdef
  have hMD : ∀ x, cj (A x) = heisX ω ^ i x * heisY ^ j x * D x := fun x => by
    simp only [hDdef, ← mul_assoc]
    rw [mul_assoc (heisX ω ^ i x), ← pow_add, show j x + 2 * j x = 3 * j x by ring, pow_mul,
      heisY_pow_three, one_pow, mul_one, ← pow_add, show i x + 2 * i x = 3 * i x by ring, pow_mul,
      heisX_pow_three hω3, one_pow, one_mul]
  have hN : ∀ x, ∃ N : Matrix (Fin 2) (Fin 2) Ω, D x = blk N := fun x =>
    exists_blk_of_comm h3' hω (hDX x) (hDY x)
  choose N hN using hN
  have hZD : ∀ Z, CR3 (Ω := Ω) Z (heisX ω) → CR3 (Ω := Ω) Z heisY →
      (∀ y, CR3 (Ω := Ω) Z (cj (A y))) → ∀ y, CR3 (Ω := Ω) Z (D y) := by
    intro Z hZX hZY hZM y
    exact ((hZY.pow_right _).mul_right (hZX.pow_right _)).mul_right (hZM y)
  have hDD : ∀ x y, CR3 (Ω := Ω) (D x) (D y) := by
    intro x y
    have hY0 : CR3 (Ω := Ω) heisY (D y) :=
      hZD _ hXY0.symm (CR3.refl _) (fun y => (hMY' y).symm) y
    have hX0 : CR3 (Ω := Ω) (heisX ω) (D y) :=
      hZD _ (CR3.refl _) hXY0 (fun y => (hMX' y).symm) y
    have hM0 : CR3 (Ω := Ω) (cj (A x)) (D y) := hZD _ (hMX' x) (hMY' x) (hMM x) y
    exact ((hY0.pow_left _).mul_left (hX0.pow_left _)).mul_left hM0
  have hNcube : ∀ x, ∃ μ : Ω, μ ≠ 0 ∧ N x ^ 3 = μ • 1 := by
    intro x
    obtain ⟨μ, hμ0, hμ⟩ := hMcube x
    refine ⟨μ, hμ0, blk_injective ?_⟩
    rw [← blk_pow, ← hN x, blk_smul, blk_one]
    have hh : CR3 (Ω := Ω) (heisY ^ (2 * j x) * heisX ω ^ (2 * i x)) (cj (A x)) :=
      ((hMY' x).symm.pow_left _).mul_left ((hMX' x).symm.pow_left _)
    have hh3 : (heisY ^ (2 * j x) * heisX ω ^ (2 * i x) : Matrix (Fin 6) (Fin 6) Ω) ^ 3 = 1 := by
      rw [((hXY0.symm.pow_left _).pow_right _).mul_pow_three, heisY_pow_pow_three,
        heisX_pow_pow_three hω3, one_mul]
    rw [hDdef]
    dsimp only
    rw [hh.mul_pow_three, hh3, one_mul, hμ]
  choose μN hμN0 hμN using hNcube
  have hNdet : ∀ x, (N x).det ≠ 0 := fun x h0 => by
    have h := congrArg Matrix.det (hμN x)
    rw [det_pow, h0, det_smul, det_one, Fintype.card_fin, mul_one] at h
    exact pow_ne_zero 2 (hμN0 x) (by rw [← h]; ring)
  have hNcomm : ∀ x y, N x * N y = N y * N x := by
    intro x y
    obtain ⟨c, hc3, hc⟩ := hDD x y
    rw [hN x, hN y, blk_mul, blk_mul, ← blk_smul] at hc
    have hc' := blk_injective hc
    have hdet := congrArg Matrix.det hc'
    rw [det_smul, det_mul, det_mul, Fintype.card_fin, mul_comm (N y).det] at hdet
    have hc2 : c ^ 2 = 1 :=
      mul_right_cancel₀ (mul_ne_zero (hNdet x) (hNdet y)) (by rw [one_mul]; exact hdet.symm)
    rwa [show c = 1 by linear_combination hc3 - c * hc2, one_smul] at hc'
  have hν : ∀ x, ∃ ν : Ω, ν ^ 3 * μN x = 1 := fun x => by
    obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq (μN x)⁻¹ (by norm_num : 0 < 3)
    exact ⟨ν, by rw [hν, inv_mul_cancel₀ (hμN0 x)]⟩
  choose ν hν using hν
  have hν0 : ∀ x, ν x ≠ 0 := fun x h => by
    have := hν x
    rw [h] at this
    simp at this
  have hN3 : ∀ x, (ν x • N x) ^ 3 = 1 := fun x => by
    rw [smul_pow, hμN x, smul_smul, hν x, one_smul]
  obtain ⟨Q, hQ, d, hd⟩ := CFSG.RankThree.SubgroupLists.exists_simultaneous_diagonal
    (fun x => ν x • N x)
    (fun x y => by rw [smul_mul_smul_comm, smul_mul_smul_comm, hNcomm x y, mul_comm (ν x)])
    (fun x => ⟨3, h3, hN3 x⟩)
  have hNQ : ∀ x, N x * Q = Q * diagonal ((ν x)⁻¹ • d x) := fun x => by
    rw [diagonal_smul, mul_smul_comm, ← hd x, smul_mul_assoc, smul_smul, inv_mul_cancel₀ (hν0 x),
      one_smul]
  have hd0 : ∀ x k, d x k ≠ 0 := fun x k h => by
    have := CFSG.RankThree.SubgroupLists.pow_eq_one_of_mul_eq_mul_diagonal hQ (hd x) (hN3 x) k
    rw [h] at this
    simp at this
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hK : IsUnit (blk Q) := (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (B := blk Q⁻¹)
      (by rw [blk_mul, Matrix.mul_nonsing_inv Q hQdet, blk_one]))
  refine ⟨hP.unit * hK.unit, ω, hω3, hω1, fun x => ⟨i x, j x, (ν x)⁻¹ * d x 0, (ν x)⁻¹ * d x 1,
    hi x, hj x, mul_ne_zero (inv_ne_zero (hν0 x)) (hd0 x 0),
    mul_ne_zero (inv_ne_zero (hν0 x)) (hd0 x 1), ?_⟩⟩
  have hF : ((hP.unit * hK.unit : GL (Fin 6) Ω) : Matrix (Fin 6) (Fin 6) Ω) = P * blk Q := by
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
  have hKX : Commute (blk Q) (heisX ω) := blk_mul_heisX Q ω
  have hKY : Commute (blk Q) heisY := blk_mul_heisY Q
  have hKc : Commute (blk Q) (heisX ω ^ i x * heisY ^ j x) :=
    (hKX.pow_right _).mul_right (hKY.pow_right _)
  have key : A x * (P * blk Q) =
      P * blk Q * (heisX ω ^ i x * heisY ^ j x * heisD ((ν x)⁻¹ * d x 0) ((ν x)⁻¹ * d x 1)) := by
    calc A x * (P * blk Q) = P * cj (A x) * blk Q := by
          rw [hcj]
          dsimp only
          rw [← mul_assoc P, ← mul_assoc P, hPP, one_mul, mul_assoc]
      _ = P * (heisX ω ^ i x * heisY ^ j x) * (blk (N x) * blk Q) := by
          rw [hMD x, hN x]
          simp only [mul_assoc]
      _ = P * (heisX ω ^ i x * heisY ^ j x) *
            (blk Q * heisD ((ν x)⁻¹ * d x 0) ((ν x)⁻¹ * d x 1)) := by
          rw [blk_mul, hNQ, ← blk_mul, blk_diagonal]
          rfl
      _ = _ := by
          rw [← mul_assoc, mul_assoc P, ← hKc.eq]
          simp only [mul_assoc]
  rw [Units.val_mul, Units.val_mul, hF, hA x, mul_assoc, key, ← mul_assoc, ← hF, Units.inv_mul,
    one_mul]

end Normal

end CFSG.StandardType.KG87B
