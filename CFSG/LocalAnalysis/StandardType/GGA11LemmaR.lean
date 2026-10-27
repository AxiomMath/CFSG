module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

open Certificates.A8Nbr476 Matrix

instance CFSG.StandardType.A11.instFactPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

namespace CFSG.StandardType.A11

private def a11lr_mu3 : Finset (ZMod 7) := {1, 2, 4}

private def a11lr_mon (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3) : M4 :=
  Matrix.of fun i j => if π i = j then (2 : ZMod 7) ^ (k i).val else 0

private def a11lr_pX (j : Fin 4) (σ : Fin 4 → Fin 4) (m : Fin 4 → ZMod 3) (s : Bool) : M4 :=
  Matrix.of fun i l => if σ i = l then
    (if i = j then 1 else if s then (2 : ZMod 7) ^ (m i).val
      else -((2 : ZMod 7) ^ (m i).val)) else 0

private def a11lr_RankOneB (X : M4) : Prop :=
  X ≠ 1 ∧ ∀ i j k l : Fin 4, (X - 1) i k * (X - 1) j l = (X - 1) i l * (X - 1) j k

private theorem a11lr_mem_mu3 {x : ZMod 7} : x ∈ a11lr_mu3 ↔ x = 1 ∨ x = 2 ∨ x = 4 := by
  simp [a11lr_mu3]

private theorem a11lr_cube_of_mem_mu3 {x : ZMod 7} (hx : x ∈ a11lr_mu3) : x ^ 3 = 1 := by
  rcases a11lr_mem_mu3.1 hx with rfl | rfl | rfl <;> decide

private theorem a11lr_ne_zero_of_mem_mu3 {x : ZMod 7} (hx : x ∈ a11lr_mu3) : x ≠ 0 := by
  rcases a11lr_mem_mu3.1 hx with rfl | rfl | rfl <;> decide

private theorem a11lr_mul_mem_mu3 {x y : ZMod 7} (hx : x ∈ a11lr_mu3) (hy : y ∈ a11lr_mu3) :
    x * y ∈ a11lr_mu3 := by
  rcases a11lr_mem_mu3.1 hx with rfl | rfl | rfl <;>
    rcases a11lr_mem_mu3.1 hy with rfl | rfl | rfl <;> decide

private theorem a11lr_inv_eq_sq_of_mem_mu3 {x : ZMod 7} (hx : x ∈ a11lr_mu3) : x⁻¹ = x ^ 2 :=
  inv_eq_of_mul_eq_one_right (by linear_combination a11lr_cube_of_mem_mu3 hx)

private theorem a11lr_step3 : ∀ c : Fin 4 → ZMod 7, (∀ i, c i ∈ a11lr_mu3) →
    ∃ d : Fin 4 → ZMod 7, (∀ i, d i ∈ a11lr_mu3) ∧ ∑ i, d i * c i = 0 ∧
      ∑ i, (d i)⁻¹ * c i ≠ 0 := by
  intro c hc
  have h7 : (7 : ZMod 7) = 0 := by decide
  obtain ⟨k, hk⟩ : ∃ k, ∑ i, c i ^ 2 + c k ^ 2 ≠ 0 := by
    by_contra H
    push_neg at H
    have h0 := H 0
    have h1 := H 1
    have h2 := H 2
    have h3 := H 3
    simp only [Fin.sum_univ_four] at h0 h1 h2 h3
    have h : c 0 ^ 2 = 0 := by
      linear_combination h0 - 3 * (h0 + h1 + h2 + h3) +
        2 * (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2) * h7
    exact a11lr_ne_zero_of_mem_mu3 (hc 0) (pow_eq_zero_iff two_ne_zero |>.1 h)
  let e : Fin 4 → ZMod 7 := fun i => if i = k then 4 else 1
  have he : ∀ i, e i ∈ a11lr_mu3 := fun i => by
    by_cases h : i = k <;> simp [e, h, a11lr_mu3]
  have hd : ∀ i, e i * c i ^ 2 ∈ a11lr_mu3 := fun i =>
    a11lr_mul_mem_mu3 (he i) (by simpa [pow_two] using a11lr_mul_mem_mu3 (hc i) (hc i))
  refine ⟨fun i => e i * c i ^ 2, hd, ?_, ?_⟩
  · have hs : ∀ i, e i * c i ^ 2 * c i = 1 + if i = k then 3 else 0 := fun i => by
      have := a11lr_cube_of_mem_mu3 (hc i)
      by_cases h : i = k
      · subst h; simp only [e, if_true]; linear_combination 4 * this
      · simp only [e, h, if_false]; linear_combination this
    simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    linear_combination h7
  · have hs : ∀ i, (e i * c i ^ 2)⁻¹ * c i = c i ^ 2 + if i = k then 15 * c k ^ 2 else 0 :=
      fun i => by
      have := a11lr_cube_of_mem_mu3 (hc i)
      rw [a11lr_inv_eq_sq_of_mem_mu3 (hd i)]
      by_cases h : i = k
      · subst h; simp only [e, if_true]; linear_combination (16 * c i ^ 2) * this
      · simp only [e, h, if_false]; linear_combination c i ^ 2 * this
    simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    intro h
    exact hk (by linear_combination h - 2 * c k ^ 2 * h7)

private theorem a11lr_vecMulVec_mul_self (u w : Fin 4 → ZMod 7) :
    vecMulVec u w * vecMulVec u w = (w ⬝ᵥ u) • vecMulVec u w := by
  rw [vecMulVec_mul_vecMulVec]; ext i j; simp [vecMulVec_apply]; ring

private theorem a11lr_inv_one_add_vecMulVec (u w : Fin 4 → ZMod 7) (h : 1 + w ⬝ᵥ u ≠ 0) :
    (1 + vecMulVec u w)⁻¹ = 1 - (1 + w ⬝ᵥ u)⁻¹ • vecMulVec u w := by
  apply Matrix.inv_eq_right_inv
  have hμ : (1 + w ⬝ᵥ u)⁻¹ * (1 + w ⬝ᵥ u) = 1 := inv_mul_cancel₀ h
  rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, a11lr_vecMulVec_mul_self, smul_smul]
  linear_combination (norm := module) -hμ • vecMulVec u w

private theorem a11lr_nt2 (u₁ w₁ u₂ w₂ : Fin 4 → ZMod 7) (hu₁ : u₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (h₁ : 1 + w₁ ⬝ᵥ u₁ ≠ 0) (h₂ : 1 + w₂ ⬝ᵥ u₂ ≠ 0)
    (h : w₂ ⬝ᵥ u₁ = 0) (h' : w₁ ⬝ᵥ u₂ ≠ 0) :
    IsTransv ((1 + vecMulVec u₁ w₁) * (1 + vecMulVec u₂ w₂) * (1 + vecMulVec u₁ w₁)⁻¹ *
      (1 + vecMulVec u₂ w₂)⁻¹) := by
  set A := vecMulVec u₁ w₁
  set B := vecMulVec u₂ w₂
  have hBA : B * A = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  have hAB : A * B = (w₁ ⬝ᵥ u₂) • vecMulVec u₁ w₂ := by
    rw [vecMulVec_mul_vecMulVec, dotProduct_comm]; ext i j; simp [vecMulVec_apply]; ring
  have hμ₁ : (1 + w₁ ⬝ᵥ u₁)⁻¹ * (1 + w₁ ⬝ᵥ u₁) = 1 := inv_mul_cancel₀ h₁
  have hμ₂ : (1 + w₂ ⬝ᵥ u₂)⁻¹ * (1 + w₂ ⬝ᵥ u₂) = 1 := inv_mul_cancel₀ h₂
  have hAA : A * A = (w₁ ⬝ᵥ u₁) • A := a11lr_vecMulVec_mul_self u₁ w₁
  have hBB : B * B = (w₂ ⬝ᵥ u₂) • B := a11lr_vecMulVec_mul_self u₂ w₂
  rw [a11lr_inv_one_add_vecMulVec u₁ w₁ h₁, a11lr_inv_one_add_vecMulVec u₂ w₂ h₂]
  set μ₁ := (1 + w₁ ⬝ᵥ u₁)⁻¹
  set μ₂ := (1 + w₂ ⬝ᵥ u₂)⁻¹
  have e1 : (1 + B) * (1 - μ₁ • A) = 1 - μ₁ • A + B := by
    rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, hBA, smul_zero]; abel
  have e2 : (1 + A) * (1 - μ₁ • A + B) = 1 + B + A * B := by
    rw [add_mul, one_mul, mul_add, mul_sub, mul_one, mul_smul_comm, hAA, smul_smul]
    linear_combination (norm := module) -hμ₁ • A
  have e3 : (1 + B + A * B) * (1 - μ₂ • B) = 1 + μ₂ • (A * B) := by
    rw [mul_sub, mul_one, mul_smul_comm, add_mul, add_mul, one_mul, hBB, mul_assoc, hBB,
      mul_smul_comm]
    linear_combination (norm := module) -hμ₂ • (B + A * B)
  have hP : (1 + A) * (1 + B) * (1 - μ₁ • A) * (1 - μ₂ • B) =
      1 + (μ₂ * (w₁ ⬝ᵥ u₂)) • vecMulVec u₁ w₂ := by
    rw [mul_assoc (1 + A), e1, e2, e3, hAB, smul_smul]
  rw [hP]
  have hc : μ₂ * (w₁ ⬝ᵥ u₂) ≠ 0 := mul_ne_zero (inv_ne_zero h₂) h'
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu₁
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw₂
  refine ⟨fun h1 => ?_, ?_, fun a b c d => ?_⟩
  · have := congrFun (congrFun (add_eq_left.1 h1) i) j
    simp [vecMulVec_apply] at this
    simp only [Pi.zero_apply] at hi hj
    rcases this with (h | h) | h | h
    exacts [inv_ne_zero h₂ h, h' h, hi h, hj h]
  · have hsub : (1 + (μ₂ * (w₁ ⬝ᵥ u₂)) • vecMulVec u₁ w₂ : M4) - 1 =
        (μ₂ * (w₁ ⬝ᵥ u₂)) • vecMulVec u₁ w₂ := by abel
    rw [hsub, smul_mul_smul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero, smul_zero]
  · have hsub : (1 + (μ₂ * (w₁ ⬝ᵥ u₂)) • vecMulVec u₁ w₂ : M4) - 1 =
        (μ₂ * (w₁ ⬝ᵥ u₂)) • vecMulVec u₁ w₂ := by abel
    rw [hsub]
    simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]; ring

private theorem a11lr_F1 : ∀ j : Fin 4, ∀ σ : Fin 4 → Fin 4, (∀ i i', σ i = σ i' → i = i') →
    σ j = j → ∀ m : Fin 4 → ZMod 3, ¬ a11lr_RankOneB (a11lr_pX j σ m false) := by
  unfold a11lr_RankOneB
  decide +kernel

private def a11lr_diag (i : Fin 4) (a : ZMod 3) : M4 := a11lr_mon 1 (Pi.single i a)

private theorem a11lr_pow2_add (a b : ZMod 3) :
    (2 : ZMod 7) ^ (a + b).val = (2 : ZMod 7) ^ a.val * (2 : ZMod 7) ^ b.val := by
  revert a b; decide +kernel

private theorem a11lr_mon_mul (π τ : Equiv.Perm (Fin 4)) (k m : Fin 4 → ZMod 3) :
    a11lr_mon π k * a11lr_mon τ m = a11lr_mon (τ * π) (fun i => k i + m (π i)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (π i)]
  · simp only [a11lr_mon, Matrix.of_apply, if_true]
    by_cases h : τ (π i) = j
    · simp only [h, if_true, Equiv.Perm.mul_apply, a11lr_pow2_add]
    · simp only [h, if_false, mul_zero, Equiv.Perm.mul_apply]
  · intro l _ hl
    simp only [a11lr_mon, Matrix.of_apply]
    rw [if_neg (fun h => hl h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ (π i)) h

private theorem a11lr_mon_one (k : Fin 4 → ZMod 3) :
    a11lr_mon 1 k = Matrix.diagonal (fun l => (2 : ZMod 7) ^ (k l).val) := by
  ext l j
  by_cases h : l = j <;> simp [a11lr_mon, Matrix.diagonal_apply, h]

private def a11lr_prodDiag (k : Fin 4 → ZMod 3) : M4 :=
  a11lr_diag 0 (k 0) * a11lr_diag 1 (k 1) * a11lr_diag 2 (k 2) * a11lr_diag 3 (k 3)

private theorem a11lr_mon_one_eq_prodDiag (k : Fin 4 → ZMod 3) :
    a11lr_mon 1 k = a11lr_prodDiag k := by
  revert k; decide +kernel

private theorem a11lr_mon_swap_castSucc_succ (i : Fin 3) :
    a11lr_mon (Equiv.swap i.castSucc i.succ) 0 =
      ![!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1],
        !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
        !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]] i := by
  fin_cases i <;> decide +kernel

private theorem a11lr_mon_d0 :
    a11lr_mon 1 (Pi.single (0 : Fin 4) (1 : ZMod 3)) =
      !![2,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  decide +kernel

private def a11lr_permMat : Equiv.Perm (Fin 4) →* M4 where
  toFun σ := a11lr_mon σ⁻¹ 0
  map_one' := by ext i j; simp [a11lr_mon, Matrix.one_apply]
  map_mul' σ τ := by
    rw [a11lr_mon_mul, _root_.mul_inv_rev]
    rfl

private theorem a11lr_permMat_mem (σ : Equiv.Perm (Fin 4)) :
    a11lr_permMat σ ∈ Submonoid.closure G314gens := by
  let g : Fin 3 → Equiv.Perm (Fin 4) := fun i => Equiv.swap i.castSucc i.succ
  have hT : σ ∈ Submonoid.closure (Set.range g) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top σ
  have hgen : ∀ i : Fin 3, a11lr_permMat (g i) ∈ Submonoid.closure G314gens := by
    intro i
    have h1 : a11lr_permMat (g i) = a11lr_mon (g i) 0 := by simp [a11lr_permMat, g]
    rw [h1, a11lr_mon_swap_castSucc_succ i]
    fin_cases i <;> exact Submonoid.subset_closure (by simp [G314gens])
  have hmem : ∀ x ∈ Set.range g, a11lr_permMat x ∈ Submonoid.closure G314gens := by
    rintro x ⟨i, rfl⟩; exact hgen i
  refine Submonoid.closure_induction
    (motive := fun x _ => a11lr_permMat x ∈ Submonoid.closure G314gens) ?_ ?_ ?_ hT
  · exact hmem
  · rw [map_one]; exact one_mem _
  · intro x y hx hy hpx hpy
    rw [map_mul]; exact mul_mem hpx hpy

private theorem a11lr_diag_mem (i : Fin 4) :
    a11lr_diag i 1 ∈ Submonoid.closure G314gens := by
  have hP : a11lr_permMat (Equiv.swap (0 : Fin 4) i) ∈ Submonoid.closure G314gens :=
    a11lr_permMat_mem _
  have hD : a11lr_diag (0 : Fin 4) 1 ∈ Submonoid.closure G314gens := by
    have hmem : a11lr_mon 1 (Pi.single (0 : Fin 4) (1 : ZMod 3)) ∈
        Submonoid.closure G314gens :=
      Submonoid.subset_closure (by rw [a11lr_mon_d0]; simp [G314gens])
    simpa [a11lr_diag] using hmem
  have hconj : a11lr_diag i 1 = a11lr_permMat (Equiv.swap (0 : Fin 4) i) *
      a11lr_diag (0 : Fin 4) 1 * a11lr_permMat (Equiv.swap (0 : Fin 4) i) := by
    fin_cases i <;> decide +kernel
  rw [hconj]
  exact mul_mem (mul_mem hP hD) hP

private theorem a11lr_diag_pow (i : Fin 4) (a : ZMod 3) :
    a11lr_diag i a = (a11lr_diag i 1) ^ a.val := by
  revert i a; decide +kernel

private theorem a11lr_diag_mem' (i : Fin 4) (a : ZMod 3) :
    a11lr_diag i a ∈ Submonoid.closure G314gens := by
  rw [a11lr_diag_pow]
  exact pow_mem (a11lr_diag_mem i) _

private theorem a11lr_prodDiag_mem (k : Fin 4 → ZMod 3) :
    a11lr_prodDiag k ∈ Submonoid.closure G314gens := by
  unfold a11lr_prodDiag
  exact mul_mem (mul_mem (mul_mem (a11lr_diag_mem' 0 (k 0)) (a11lr_diag_mem' 1 (k 1)))
    (a11lr_diag_mem' 2 (k 2))) (a11lr_diag_mem' 3 (k 3))

private theorem a11lr_mon_mem_closure (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3) :
    a11lr_mon π k ∈ Submonoid.closure G314gens := by
  have h1 : a11lr_mon π k = a11lr_mon 1 k * a11lr_mon π 0 := by
    rw [a11lr_mon_mul]
    simp
  rw [h1]
  refine mul_mem ?_ ?_
  · rw [a11lr_mon_one_eq_prodDiag]
    exact a11lr_prodDiag_mem k
  · have h2 : a11lr_mon π 0 = a11lr_permMat π⁻¹ := by simp [a11lr_permMat]
    rw [h2]
    exact a11lr_permMat_mem π⁻¹

private theorem a11lr_vecMul_ev (M : M4) (i : Fin 4) : Matrix.vecMul (ev i) M = M i := by
  change Pi.single i 1 ᵥ* M = M i
  rw [Matrix.single_one_vecMul]
  ext l; rfl

private theorem a11lr_mon_row (π : Equiv.Perm (Fin 4)) (k : Fin 4 → ZMod 3) (i : Fin 4) :
    a11lr_mon π k i = (2 : ZMod 7) ^ (k i).val • ev (π i) := by
  ext l
  by_cases h : π i = l
  · subst h; simp [a11lr_mon, ev, Pi.smul_apply, Pi.single_apply]
  · simp [a11lr_mon, ev, Pi.smul_apply, Pi.single_apply, h]

private theorem a11lr_minors_of_rank_one (M : M4) (hM : M.rank = 1) :
    ∀ i j k l : Fin 4, M i k * M j l = M i l * M j k := by
  intro i j k l
  by_contra h
  have hle : (M.submatrix ![i,j] ![k,l]).rank ≤ 1 := by
    have := Matrix.rank_submatrix_le M ![i,j] ![k,l]
    rwa [hM] at this
  have hdet : (M.submatrix ![i,j] ![k,l]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, cons_val_zero, cons_val_one, cons_val_fin_one]
    intro hd
    exact h (sub_eq_zero.mp hd)
  have h2 : (M.submatrix ![i,j] ![k,l]).rank = 2 := by
    rw [Matrix.rank_of_det_ne_zero hdet]
    simp
  omega

private theorem a11lr_rank_one_factor (M : M4) (hM : M.rank = 1) :
    ∃ u w : Fin 4 → ZMod 7, u ≠ 0 ∧ w ≠ 0 ∧ M = vecMulVec u w := by
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, Matrix.rank_zero] at hM
    exact Nat.zero_ne_one hM
  have hmin := a11lr_minors_of_rank_one M hM
  obtain ⟨i0, j0, hij⟩ : ∃ i0 j0, M i0 j0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hM0 (by ext i j; exact h i j)
  refine ⟨fun i => M i j0 * (M i0 j0)⁻¹, fun j => M i0 j, ?_, ?_, ?_⟩
  · intro hu
    have := congrFun hu i0
    simp only [Pi.zero_apply] at this
    rw [mul_inv_cancel₀ hij] at this
    exact one_ne_zero this
  · intro hw
    exact hij (congrFun hw j0)
  · ext i j
    rw [vecMulVec_apply]
    calc M i j = M i j * M i0 j0 * (M i0 j0)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hij, mul_one]
      _ = M i j0 * M i0 j * (M i0 j0)⁻¹ := by rw [← hmin i i0 j0 j]
      _ = M i j0 * (M i0 j0)⁻¹ * M i0 j := by ring

private theorem a11lr_rankOneB_of_rank (r : M4) (hM : (r - 1).rank = 1) :
    a11lr_RankOneB r := by
  have hmin := a11lr_minors_of_rank_one (r - 1) hM
  refine ⟨?_, ?_⟩
  · intro h
    rw [h, sub_self, Matrix.rank_zero] at hM
    exact Nat.zero_ne_one hM
  · intro i j k l
    exact hmin i j k l

private theorem a11lr_one_add_dot_ne_zero (A : Submonoid M4)
    (hinv : ∀ a ∈ A, IsUnit a.det ∧ a⁻¹ ∈ A)
    {u w : Fin 4 → ZMod 7} (h : (1 + vecMulVec u w) ∈ A) :
    1 + w ⬝ᵥ u ≠ 0 := by
  have hdet : (1 + vecMulVec u w).det = 1 + w ⬝ᵥ u := by
    rw [Matrix.vecMulVec_eq (ι := Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hunit := (hinv _ h).1
  rw [hdet] at hunit
  exact hunit.ne_zero

private theorem a11lr_nt2_iff (A : Submonoid M4)
    (hinv : ∀ a ∈ A, IsUnit a.det ∧ a⁻¹ ∈ A)
    (hNT : ∀ t ∈ A, ¬ IsTransv t)
    {u w uγ wγ : Fin 4 → ZMod 7}
    (hu : u ≠ 0) (hw : w ≠ 0) (huγ : uγ ≠ 0) (hwγ : wγ ≠ 0)
    (hr : (1 + vecMulVec u w) ∈ A) (hγ : (1 + vecMulVec uγ wγ) ∈ A) :
    wγ ⬝ᵥ u = 0 ↔ w ⬝ᵥ uγ = 0 := by
  have h1 := a11lr_one_add_dot_ne_zero A hinv hr
  have h2 := a11lr_one_add_dot_ne_zero A hinv hγ
  constructor
  · intro hzero
    by_contra hne
    exact hNT _ (mul_mem (mul_mem (mul_mem hr hγ) (hinv _ hr).2) (hinv _ hγ).2)
      (a11lr_nt2 u w uγ wγ hu hwγ h1 h2 hzero hne)
  · intro hzero
    by_contra hne
    exact hNT _ (mul_mem (mul_mem (mul_mem hγ hr) (hinv _ hγ).2) (hinv _ hr).2)
      (a11lr_nt2 uγ wγ u w huγ hw h2 h1 hzero hne)

private theorem a11lr_t_uγ_ne (j : Fin 4) (hj : j ≠ (0 : Fin 4)) (a : ZMod 7) (ha : a ≠ 0) :
    (ev 0 - a⁻¹ • ev j : Fin 4 → ZMod 7) ≠ 0 := by
  intro h
  have := congrFun h j
  simp [ev, Pi.single_apply, Pi.sub_apply, Pi.smul_apply, Ne.symm hj] at this
  exact ha (inv_eq_zero.mp (neg_eq_zero.mp this))

private theorem a11lr_t_wγ_ne (j : Fin 4) (hj : j ≠ (0 : Fin 4)) (a : ZMod 7) (ha : a ≠ 0) :
    (a • ev j - ev 0 : Fin 4 → ZMod 7) ≠ 0 := by
  intro h
  have := congrFun h j
  simp [ev, Pi.single_apply, Pi.sub_apply, Pi.smul_apply, Ne.symm hj] at this
  exact ha (sub_eq_zero.mp this)

private def a11lr_log (a : ZMod 7) : ZMod 3 :=
  if a = 1 then 0 else if a = 2 then 1 else 2

private theorem a11lr_log_mem (a : ZMod 7) (ha : a ∈ a11lr_mu3) :
    (2 : ZMod 7) ^ (a11lr_log a).val = a := by
  revert a; decide +kernel

private theorem a11lr_diag_one_eq (j : Fin 4) :
    a11lr_diag j 1 = 1 + vecMulVec (ev j) (ev j) := by
  fin_cases j <;> decide +kernel

private def a11lr_tkey (i j : Fin 4) (a : ZMod 7) : Fin 4 → ZMod 3 :=
  fun l => if l = i then a11lr_log a else if l = j then a11lr_log a⁻¹ else 0

private theorem a11lr_tkey_eq (j : Fin 4) (hj : j ≠ (0 : Fin 4)) (a : ZMod 7)
    (ha : a ∈ a11lr_mu3) :
    a11lr_mon (Equiv.swap (0 : Fin 4) j) (a11lr_tkey 0 j a) =
      1 + vecMulVec (ev 0 - a⁻¹ • ev j) (a • ev j - ev 0) := by
  revert j a; decide +kernel

private theorem a11lr_step3' (c : Fin 4 → ZMod 7) (hc : ∀ i, c i ∈ a11lr_mu3) :
    ∃ k : Fin 4 → ZMod 3, (∑ i, (2 : ZMod 7) ^ ((k i).val) * c i = 0) ∧
      (∑ i, ((2 : ZMod 7) ^ ((k i).val))⁻¹ * c i ≠ 0) := by
  obtain ⟨d, hd, h1, h2⟩ := a11lr_step3 c hc
  refine ⟨fun i => a11lr_log (d i), ?_, ?_⟩
  · rw [show (∑ i, (2 : ZMod 7) ^ ((a11lr_log (d i)).val) * c i) = ∑ i, d i * c i by
      apply Finset.sum_congr rfl
      intro i _
      rw [a11lr_log_mem (d i) (hd i)]]
    exact h1
  · rw [show (∑ i, ((2 : ZMod 7) ^ ((a11lr_log (d i)).val))⁻¹ * c i) =
        ∑ i, (d i)⁻¹ * c i by
      apply Finset.sum_congr rfl
      intro i _
      rw [a11lr_log_mem (d i) (hd i)]]
    exact h2

private theorem a11lr_diagonal_mul_vecMulVec (d u w : Fin 4 → ZMod 7) :
    Matrix.diagonal d * vecMulVec u w = vecMulVec (fun i => d i * u i) w := by
  ext i j; simp [Matrix.diagonal_mul, vecMulVec_apply, mul_assoc]

private theorem a11lr_vecMulVec_mul_diagonal (d u w : Fin 4 → ZMod 7) :
    vecMulVec u w * Matrix.diagonal d = vecMulVec u (fun j => w j * d j) := by
  ext i j; simp [Matrix.mul_diagonal, vecMulVec_apply, mul_assoc]

private theorem a11lr_neg_pow_log (a : ZMod 7) (ha : a = 3 ∨ a = 5 ∨ a = 6) :
    -((2 : ZMod 7) ^ ((if a = 3 then 2 else if a = 5 then 1 else 0 : ZMod 3)).val) = a := by
  rcases ha with rfl | rfl | rfl <;> decide

private theorem a11lr_mu3_mul_compl {p q : ZMod 7} (hp : p ≠ 0) (hq : q ≠ 0)
    (hp3 : p ∉ a11lr_mu3) (hq3 : q ∉ a11lr_mu3) : p * q ∈ a11lr_mu3 := by
  revert p q
  set_option synthInstance.maxSize 512 in
  decide +kernel

private theorem a11lr_dot_smul_sub (a : ZMod 7) (j : Fin 4) (u : Fin 4 → ZMod 7) :
    (a • ev j - ev 0) ⬝ᵥ u = a * u j - u 0 := by
  simp only [ev, sub_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul]

private theorem a11lr_dot_sub_smul (a : ZMod 7) (j : Fin 4) (w : Fin 4 → ZMod 7) :
    w ⬝ᵥ (ev 0 - a⁻¹ • ev j) = w 0 - a⁻¹ * w j := by
  simp only [ev, dotProduct_sub, dotProduct_smul, dotProduct_single_one, smul_eq_mul]

private theorem a11lr_x_cancel (u w : Fin 4 → ZMod 7) (hu0 : u 0 ≠ 0) (hw0 : w 0 ≠ 0)
    (j : Fin 4) : (u j * w j * (u 0 * w 0)⁻¹) * (u 0 * w 0) = u j * w j := by
  rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero hu0 hw0), mul_one]

private theorem a11lr_coset_fact {u0 uj w0 wj : ZMod 7}
    (hu0 : u0 ≠ 0) (hw0 : w0 ≠ 0) (huj : uj ≠ 0) (hwj : wj ≠ 0)
    (h : ∀ a ∈ a11lr_mu3, (a * uj = u0 ↔ a * w0 = wj)) :
    uj * wj * (u0 * w0)⁻¹ ∈ a11lr_mu3 := by
  have hp : uj * u0⁻¹ ≠ 0 := mul_ne_zero huj (inv_ne_zero hu0)
  have hq : wj * w0⁻¹ ≠ 0 := mul_ne_zero hwj (inv_ne_zero hw0)
  have hpq : ∀ a ∈ a11lr_mu3, (a * (uj * u0⁻¹) = 1 ↔ a = wj * w0⁻¹) := by
    intro a ha
    have h0 := h a ha
    have e1 : (a * uj = u0) ↔ (a * (uj * u0⁻¹) = 1) := by
      constructor
      · intro hh
        rw [show a * (uj * u0⁻¹) = a * uj * u0⁻¹ by ring, hh, mul_inv_cancel₀ hu0]
      · intro hh
        calc a * uj = a * (uj * u0⁻¹ * u0) := by
              rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one]
          _ = a * (uj * u0⁻¹) * u0 := by ring
          _ = 1 * u0 := by rw [hh]
          _ = u0 := one_mul _
    have e2 : (a * w0 = wj) ↔ (a = wj * w0⁻¹) := by
      constructor
      · intro hh
        calc a = a * w0 * w0⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hw0, mul_one]
          _ = wj * w0⁻¹ := by rw [hh]
      · intro hh
        calc a * w0 = wj * w0⁻¹ * w0 := by rw [hh]
          _ = wj := by rw [mul_assoc, inv_mul_cancel₀ hw0, mul_one]
    rw [← e1, ← e2]
    exact h0
  have hpq_mul : uj * wj * (u0 * w0)⁻¹ = (uj * u0⁻¹) * (wj * w0⁻¹) := by
    rw [_root_.mul_inv_rev]; ring
  rw [hpq_mul]
  by_cases hq3 : wj * w0⁻¹ ∈ a11lr_mu3
  · have h1 : (wj * w0⁻¹) * (uj * u0⁻¹) = 1 := (hpq _ hq3).mpr rfl
    rw [mul_comm, h1]
    exact a11lr_mem_mu3.mpr (Or.inl rfl)
  · have hp3 : uj * u0⁻¹ ∉ a11lr_mu3 := by
      intro hp3
      have hpinv : (uj * u0⁻¹)⁻¹ ∈ a11lr_mu3 := by
        rw [a11lr_inv_eq_sq_of_mem_mu3 hp3]
        simpa [pow_two] using a11lr_mul_mem_mu3 hp3 hp3
      have h1 : (uj * u0⁻¹)⁻¹ = wj * w0⁻¹ := (hpq _ hpinv).mp (by rw [inv_mul_cancel₀ hp])
      exact hq3 (h1 ▸ hpinv)
    exact a11lr_mu3_mul_compl hp hq hp3 hq3

private theorem a11lr_rankOne_mon (A : Submonoid M4)
    (hΓ : G314gens ⊆ (A : Set M4))
    (hinv : ∀ a ∈ A, IsUnit a.det ∧ a⁻¹ ∈ A)
    (hNT : ∀ t ∈ A, ¬ IsTransv t)
    (h89 : ∀ h ∈ A, ∀ j : Fin 4, Matrix.vecMul (ev j) h = ev j → Good9B j h)
    {r : M4} (hr : r ∈ A) (hrank : (r - 1).rank = 1) :
    ∃ π k, r = a11lr_mon π k := by
  have hΓA : Submonoid.closure G314gens ≤ A := Submonoid.closure_le.mpr hΓ
  obtain ⟨u, w, hu, hw, hfac⟩ := a11lr_rank_one_factor (r - 1) hrank
  have hr_eq : r = 1 + vecMulVec u w := by rw [← hfac]; abel
  have hdot : 1 + w ⬝ᵥ u ≠ 0 :=
    a11lr_one_add_dot_ne_zero A hinv (by rw [← hr_eq]; exact hr)
  by_cases hcase : ∃ j : Fin 4, u j = 0
  · obtain ⟨j, huj⟩ := hcase
    have hrow : Matrix.vecMul (ev j) r = ev j := by
      rw [hr_eq, Matrix.vecMul_add, Matrix.vecMul_one]
      have hv : Matrix.vecMul (ev j) (vecMulVec u w) = u j • w := by
        change Pi.single j 1 ᵥ* vecMulVec u w = u j • w
        rw [Matrix.single_one_vecMul]
        ext l; simp [Matrix.row, vecMulVec_apply]
      rw [hv, huj, zero_smul, add_zero]
    obtain ⟨-, π, g, hπj, hrows, hsign⟩ := h89 r hr j hrow
    rcases hsign with hmu | hneg
    · let k : Fin 4 → ZMod 3 := fun i => if i = j then 0 else a11lr_log (g i)
      refine ⟨π, k, ?_⟩
      ext i l
      by_cases hij : i = j
      · rw [hij]
        have hrj : r j = ev j := by rw [← a11lr_vecMul_ev r j]; exact hrow
        have hki : k j = 0 := by simp [k]
        have hmj : a11lr_mon π k j = ev j := by
          rw [a11lr_mon_row, hki]; simp [hπj]
        rw [hrj, hmj]
      · have hri : r i = g i • ev (π i) := by rw [← a11lr_vecMul_ev r i]; exact hrows i hij
        have hki : k i = a11lr_log (g i) := by simp [k, hij]
        have hgi : g i ∈ a11lr_mu3 := a11lr_mem_mu3.mpr (hmu i hij)
        have hmi : a11lr_mon π k i = g i • ev (π i) := by
          rw [a11lr_mon_row, hki, a11lr_log_mem (g i) hgi]
        rw [hri, hmi]
    · let m : Fin 4 → ZMod 3 :=
          fun i => if i = j then 0 else if g i = 3 then 2 else if g i = 5 then 1 else 0
      have heq : r = a11lr_pX j π m false := by
        ext i l
        by_cases hij : i = j
        · rw [hij]
          have hrj : r j = ev j := by rw [← a11lr_vecMul_ev r j]; exact hrow
          have hpj : a11lr_pX j π m false j = ev j := by
            ext l; simp [a11lr_pX, hπj, ev, Pi.single_apply, eq_comm]
          rw [hrj, hpj]
        · have hri : r i = g i • ev (π i) := by rw [← a11lr_vecMul_ev r i]; exact hrows i hij
          have hm : -((2 : ZMod 7) ^ ((m i).val)) = g i := by
            simp only [m, if_neg hij]
            exact a11lr_neg_pow_log (g i) (hneg i hij)
          have hpi : a11lr_pX j π m false i = g i • ev (π i) := by
            ext l
            by_cases h : π i = l
            · subst h
              have hft : ¬ ((false : Bool) = true) := by decide
              simp only [a11lr_pX, Matrix.of_apply, if_true, if_neg hij, if_neg hft,
                Pi.smul_apply, ev, Pi.single_eq_same, mul_one, smul_eq_mul]
              exact hm
            · simp [a11lr_pX, h, Ne.symm h, ev, Pi.single_apply]
          rw [hri, hpi]
      have hrk : a11lr_RankOneB r := a11lr_rankOneB_of_rank r hrank
      rw [heq] at hrk
      exact (a11lr_F1 j π (fun i i' h => π.injective h) hπj m hrk).elim
  · push_neg at hcase
    have hw0 : ∀ j, w j ≠ 0 := by
      intro j
      have hevj : (ev j : Fin 4 → ZMod 7) ≠ 0 := by
        intro h; have := congrFun h j; simp [ev] at this
      have hiff := a11lr_nt2_iff A hinv hNT hu hw hevj hevj
        (by rw [← hr_eq]; exact hr)
        (by rw [← a11lr_diag_one_eq j]; exact hΓA (a11lr_diag_mem j))
      simp only [ev, single_one_dotProduct, dotProduct_single_one] at hiff
      exact fun hwj => hcase j (hiff.mpr hwj)
    have hrelT : ∀ j : Fin 4, j ≠ (0 : Fin 4) → ∀ a ∈ a11lr_mu3,
        (a * u j = u 0 ↔ a * w 0 = w j) := by
      intro j hj a ha
      have hanej : a ≠ 0 := a11lr_ne_zero_of_mem_mu3 ha
      have huγ := a11lr_t_uγ_ne j hj a hanej
      have hwγ := a11lr_t_wγ_ne j hj a hanej
      have hγ : (1 + vecMulVec (ev 0 - a⁻¹ • ev j) (a • ev j - ev 0)) ∈ A := by
        rw [← a11lr_tkey_eq j hj a ha]
        exact hΓA (a11lr_mon_mem_closure _ _)
      have hiff := a11lr_nt2_iff A hinv hNT hu hw huγ hwγ
        (by rw [← hr_eq]; exact hr) hγ
      rw [a11lr_dot_smul_sub, a11lr_dot_sub_smul] at hiff
      constructor
      · intro hh
        have h2 : w 0 = a⁻¹ * w j := sub_eq_zero.mp (hiff.mp (sub_eq_zero.mpr hh))
        calc a * w 0 = a * (a⁻¹ * w j) := by rw [h2]
          _ = w j := by rw [← mul_assoc, mul_inv_cancel₀ hanej, one_mul]
      · intro hh
        have h2 : w 0 = a⁻¹ * w j := by
          rw [← hh, ← mul_assoc, inv_mul_cancel₀ hanej, one_mul]
        exact sub_eq_zero.mp (hiff.mpr (sub_eq_zero.mpr h2))
    have hcoset : ∀ j, u j * w j * (u 0 * w 0)⁻¹ ∈ a11lr_mu3 := by
      intro j
      by_cases hj : j = (0 : Fin 4)
      · subst hj
        rw [mul_inv_cancel₀ (mul_ne_zero (hcase 0) (hw0 0))]
        exact a11lr_mem_mu3.mpr (Or.inl rfl)
      · exact a11lr_coset_fact (hcase 0) (hw0 0) (hcase j) (hw0 j) (hrelT j hj)
    let c : Fin 4 → ZMod 7 := fun j => u j * w j * (u 0 * w 0)⁻¹
    have hc : ∀ i, c i ∈ a11lr_mu3 := hcoset
    obtain ⟨k, hk1, hk2⟩ := a11lr_step3' c hc
    let d : Fin 4 → ZMod 7 := fun i => (2 : ZMod 7) ^ (k i).val
    have hk1' : ∑ i, d i * c i = 0 := hk1
    have hk2' : ∑ i, (d i)⁻¹ * c i ≠ 0 := hk2
    have hd0 : ∀ i, d i ≠ 0 := fun i => pow_ne_zero _ (by decide : (2 : ZMod 7) ≠ 0)
    let δ : M4 := a11lr_mon 1 k
    have hδ : δ = Matrix.diagonal d := by
      change a11lr_mon 1 k = Matrix.diagonal d
      rw [a11lr_mon_one]
    have hδA : δ ∈ A := hΓA (a11lr_mon_mem_closure 1 k)
    have hδdet : IsUnit δ.det := (hinv δ hδA).1
    have hδinv : δ⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
      apply Matrix.inv_eq_right_inv
      rw [hδ, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.diagonal_apply, mul_inv_cancel₀ (hd0 i)]
      · simp [Matrix.diagonal_apply, h]
    let r' : M4 := δ⁻¹ * r * δ
    have hr'A : r' ∈ A := mul_mem (mul_mem (hinv δ hδA).2 hr) hδA
    let u₂ : Fin 4 → ZMod 7 := fun i => (d i)⁻¹ * u i
    let w₂ : Fin 4 → ZMod 7 := fun j => w j * d j
    have hr'eq : r' = 1 + vecMulVec u₂ w₂ := by
      have hδmul : δ⁻¹ * δ = 1 := Matrix.nonsing_inv_mul δ hδdet
      calc δ⁻¹ * r * δ = δ⁻¹ * (1 + vecMulVec u w) * δ := by rw [hr_eq]
        _ = δ⁻¹ * δ + δ⁻¹ * vecMulVec u w * δ := by noncomm_ring
        _ = 1 + δ⁻¹ * vecMulVec u w * δ := by rw [hδmul]
        _ = 1 + vecMulVec u₂ w₂ := by
              rw [hδinv, hδ, a11lr_diagonal_mul_vecMulVec, a11lr_vecMulVec_mul_diagonal]
    have hw₂ : w₂ ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simp only [Pi.zero_apply, w₂] at h0
      exact mul_ne_zero (hw0 0) (hd0 0) h0
    have h2' : 1 + w₂ ⬝ᵥ u₂ ≠ 0 :=
      a11lr_one_add_dot_ne_zero A hinv (by rw [← hr'eq]; exact hr'A)
    have hzero' : w₂ ⬝ᵥ u = 0 := by
      have h1 : w₂ ⬝ᵥ u = (∑ j, d j * c j) * (u 0 * w 0) := by
        rw [dotProduct, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [w₂, c]
        rw [show d j * (u j * w j * (u 0 * w 0)⁻¹) * (u 0 * w 0) = w j * d j * u j by
              rw [mul_assoc, a11lr_x_cancel u w (hcase 0) (hw0 0) j]
              ring]
      rw [h1, hk1', zero_mul]
    have hne' : w ⬝ᵥ u₂ ≠ 0 := by
      have h1 : w ⬝ᵥ u₂ = (∑ j, (d j)⁻¹ * c j) * (u 0 * w 0) := by
        rw [dotProduct, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [u₂, c]
        rw [show (d j)⁻¹ * (u j * w j * (u 0 * w 0)⁻¹) * (u 0 * w 0) =
              w j * ((d j)⁻¹ * u j) by
              rw [mul_assoc, a11lr_x_cancel u w (hcase 0) (hw0 0) j]
              ring]
      rw [h1]
      exact mul_ne_zero hk2' (mul_ne_zero (hcase 0) (hw0 0))
    have htrans := a11lr_nt2 u w u₂ w₂ (fun h => hcase 0 (congrFun h 0)) hw₂ hdot h2' hzero' hne'
    refine (hNT _ ?_ htrans).elim
    rw [← hr_eq, ← hr'eq]
    exact mul_mem (mul_mem (mul_mem hr hr'A) (hinv _ hr).2) (hinv _ hr'A).2

theorem a11LemmaRInput_holds : A11LemmaRInput := by
  intro A hΓ hinv hNT h89 r hr hrank
  obtain ⟨π, k, hrk⟩ := a11lr_rankOne_mon A hΓ hinv hNT h89 hr hrank
  rw [hrk]
  exact a11lr_mon_mem_closure π k

end CFSG.StandardType.A11

end
