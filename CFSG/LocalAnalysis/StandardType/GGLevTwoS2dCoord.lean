module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin
open scoped Matrix

theorem levTwoS2d_root_eq (n : ℕ) : (LevTwoType.D n).root = cartanD n := by
  change (CartanMatrix.D n)ᵀ = cartanD n
  rw [cartanD_eq]
  ext i j
  simp only [Matrix.transpose_apply, CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> omega

theorem levTwoS2d_isRt_iff (n : ℕ) (hn : n ≠ 1) (v : Fin n → ℤ) :
    IsRt (isFiniteType_cartanD n) v ↔
      ∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
        toStdD n v = Pi.single i s + Pi.single j t := by
  have h1 : IsRt (isFiniteType_cartanD n) v ↔ v ∈ roots (isFiniteType_cartanD n) ∅ := by
    constructor
    · rintro ⟨w, j, rfl⟩; exact Or.inl ⟨w, j, rfl⟩
    · rintro (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩)
      · exact ⟨w, j, rfl⟩
      · exact absurd hj (Set.notMem_empty j)
  rw [h1, rootsD_eq n hn]
  simp only [Set.mem_setOf_eq]

private theorem levTwoS2d_single_adj (n : ℕ) (i : Fin n) (h : i.val + 2 < n) :
    weylAction (isFiniteType_cartanD n)
        (sg (isFiniteType_cartanD n) i * sg (isFiniteType_cartanD n) ⟨i.val + 1, by omega⟩)
        (Pi.single i 1) = Pi.single (⟨i.val + 1, by omega⟩ : Fin n) 1 := by
  set j : Fin n := ⟨i.val + 1, by omega⟩ with hj
  have hjval : (j : ℕ) = i.val + 1 := by rw [hj]
  have hij : i ≠ j := by rw [hj]; exact Fin.ne_of_val_ne (by simp)
  have hAij : cartanD n i j = -1 := by
    have hc : (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
        (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n) :=
      Or.inl ⟨by omega, by omega⟩
    rw [cartanD, Matrix.of_apply, if_neg hij, if_pos hc]
  have hAji : cartanD n j i = -1 := by
    have hc : (j.val + 1 = i.val ∧ i.val + 1 < n) ∨ (i.val + 1 = j.val ∧ j.val + 1 < n) ∨
        (j.val + 3 = n ∧ i.val + 1 = n) ∨ (i.val + 3 = n ∧ j.val + 1 = n) :=
      Or.inr (Or.inl ⟨by omega, by omega⟩)
    rw [cartanD, Matrix.of_apply, if_neg (Ne.symm hij), if_pos hc]
  have step1 : weylAction (isFiniteType_cartanD n) (sg (isFiniteType_cartanD n) j)
      (Pi.single i 1) = Pi.single i 1 + Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk
      rw [weylAction_simple, reflection_apply_coroot, coroot_single, hAji]
      simp
    · rw [weylAction_simple, reflection_apply_coroot]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hk,
        mul_zero, sub_zero]
      ring
  have step2 : weylAction (isFiniteType_cartanD n) (sg (isFiniteType_cartanD n) i)
      (Pi.single i 1 + Pi.single j 1) = Pi.single j 1 := by
    rw [map_add, weylAction_simple_single, weylAction_simple, reflection_apply_coroot,
      coroot_single, hAij]
    module
  rw [weylAction_mul_apply, step1, step2]

theorem levTwoS2d_cartanD_adj (n : ℕ) (i : Fin n) (h : i.val + 2 < n) :
    cartanD n i ⟨i.val + 1, by omega⟩ = -1 := by
  have hij : i ≠ (⟨i.val + 1, by omega⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
  have hc : (i.val + 1 = (⟨i.val + 1, by omega⟩ : Fin n).val ∧
      (⟨i.val + 1, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨i.val + 1, by omega⟩ : Fin n).val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ (⟨i.val + 1, by omega⟩ : Fin n).val + 1 = n) ∨
      ((⟨i.val + 1, by omega⟩ : Fin n).val + 3 = n ∧ i.val + 1 = n) :=
    Or.inl ⟨by simp, by simp; omega⟩
  rw [cartanD, Matrix.of_apply, if_neg hij, if_pos hc]

theorem levTwoS2d_cartanD_bond_nm2 (n : ℕ) (hn : 3 ≤ n) :
    cartanD n ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ = -1 := by
  have hij : (⟨n - 3, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ :=
    Fin.ne_of_val_ne (by simp; omega)
  have hc : ((⟨n - 3, by omega⟩ : Fin n).val + 1 = (⟨n - 2, by omega⟩ : Fin n).val ∧
      (⟨n - 2, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨n - 2, by omega⟩ : Fin n).val + 1 = (⟨n - 3, by omega⟩ : Fin n).val ∧
        (⟨n - 3, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨n - 3, by omega⟩ : Fin n).val + 3 = n ∧
        (⟨n - 2, by omega⟩ : Fin n).val + 1 = n) ∨
      ((⟨n - 2, by omega⟩ : Fin n).val + 3 = n ∧
        (⟨n - 3, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inl ⟨by simp; omega, by simp; omega⟩
  rw [cartanD, Matrix.of_apply, if_neg hij, if_pos hc]

theorem levTwoS2d_cartanD_bond_nm1 (n : ℕ) (hn : 3 ≤ n) :
    cartanD n ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ = -1 := by
  have hij : (⟨n - 3, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ :=
    Fin.ne_of_val_ne (by simp; omega)
  have hc : ((⟨n - 3, by omega⟩ : Fin n).val + 1 = (⟨n - 1, by omega⟩ : Fin n).val ∧
      (⟨n - 1, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨n - 1, by omega⟩ : Fin n).val + 1 = (⟨n - 3, by omega⟩ : Fin n).val ∧
        (⟨n - 3, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨n - 3, by omega⟩ : Fin n).val + 3 = n ∧
        (⟨n - 1, by omega⟩ : Fin n).val + 1 = n) ∨
      ((⟨n - 1, by omega⟩ : Fin n).val + 3 = n ∧
        (⟨n - 3, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inr (Or.inr (Or.inl ⟨by simp; omega, by simp; omega⟩))
  rw [cartanD, Matrix.of_apply, if_neg hij, if_pos hc]

theorem levTwoS2d_cartanD_bond_nm1' (n : ℕ) (hn : 3 ≤ n) :
    cartanD n ⟨n - 1, by omega⟩ ⟨n - 3, by omega⟩ = -1 := by
  have hij : (⟨n - 1, by omega⟩ : Fin n) ≠ ⟨n - 3, by omega⟩ :=
    Fin.ne_of_val_ne (by simp; omega)
  have hc : ((⟨n - 1, by omega⟩ : Fin n).val + 1 = (⟨n - 3, by omega⟩ : Fin n).val ∧
      (⟨n - 3, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨n - 3, by omega⟩ : Fin n).val + 1 = (⟨n - 1, by omega⟩ : Fin n).val ∧
        (⟨n - 1, by omega⟩ : Fin n).val + 1 < n) ∨
      ((⟨n - 1, by omega⟩ : Fin n).val + 3 = n ∧
        (⟨n - 3, by omega⟩ : Fin n).val + 1 = n) ∨
      ((⟨n - 3, by omega⟩ : Fin n).val + 3 = n ∧
        (⟨n - 1, by omega⟩ : Fin n).val + 1 = n) :=
    Or.inr (Or.inr (Or.inr ⟨by simp; omega, by simp; omega⟩))
  rw [cartanD, Matrix.of_apply, if_neg hij, if_pos hc]

end CFSG.StandardType.LevTwo
