module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType.SporadicShape

private def m7i_e1 : Fin 4 → ZMod 7 := ![1, 0, 0, 0]

private def m7i_e2 : Fin 4 → ZMod 7 := ![0, 1, 0, 0]

private def m7i_e3 : Fin 4 → ZMod 7 := ![0, 0, 1, 0]

private def m7i_e4 : Fin 4 → ZMod 7 := ![0, 0, 0, 1]

private def m7i_u1 : Fin 4 → ZMod 7 := ![5, 2, 5, 5]

private def m7i_u2 : Fin 4 → ZMod 7 := ![0, 5, 2, 5]

private def m7i_u3 : Fin 4 → ZMod 7 := ![0, 0, 5, 2]

private def m7i_u4 : Fin 4 → ZMod 7 := ![0, 0, 0, 5]

private def m7i_N (v : Fin 4 → ZMod 7) : Fin 4 → ZMod 7 :=
  Matrix.vecMul v !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] - v

private theorem m7i_vecMul_J (v : Fin 4 → ZMod 7) :
    Matrix.vecMul v !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] =
      ![v 0, v 0 + v 1, v 1 + v 2, v 2 + v 3] := by
  ext i
  fin_cases i <;>
    simp [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.head_cons]

private theorem m7i_N_eq (v : Fin 4 → ZMod 7) :
    m7i_N v = ![0, v 0, v 1, v 2] := by
  unfold m7i_N
  rw [m7i_vecMul_J]
  ext i
  fin_cases i <;> simp

private theorem m7i_N_vec (a b c d : ZMod 7) :
    m7i_N ![a, b, c, d] = ![0, a, b, c] := by
  unfold m7i_N
  rw [m7i_vecMul_J]
  ext i
  fin_cases i <;> simp

private theorem m7i_NN (v : Fin 4 → ZMod 7) :
    m7i_N (m7i_N v) = ![0, 0, v 0, v 1] := by
  rw [m7i_N_eq v, m7i_N_vec 0 (v 0) (v 1) (v 2)]

private theorem m7i_NNN (v : Fin 4 → ZMod 7) :
    m7i_N (m7i_N (m7i_N v)) = ![0, 0, 0, v 0] := by
  rw [m7i_NN v, m7i_N_vec 0 0 (v 0) (v 1)]

private theorem m7i_N_mem {W : Submodule (ZMod 7) (Fin 4 → ZMod 7)}
    (hJ : ∀ v ∈ W,
      Matrix.vecMul v !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] ∈ W)
    {v : Fin 4 → ZMod 7} (hv : v ∈ W) : m7i_N v ∈ W := by
  unfold m7i_N
  exact Submodule.sub_mem W (hJ v hv) hv

private theorem m7i_e4B :
    Matrix.vecMul m7i_e4
      !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5] = m7i_u1 := by
  ext i
  fin_cases i <;> decide

private theorem m7i_u1N : m7i_N m7i_u1 = m7i_u2 := m7i_N_vec 5 2 5 5

private theorem m7i_u2N : m7i_N m7i_u2 = m7i_u3 := m7i_N_vec 0 5 2 5

private theorem m7i_u3N : m7i_N m7i_u3 = m7i_u4 := m7i_N_vec 0 0 5 2

private theorem m7i_comb3 : (3 : ZMod 7) • m7i_u3 + m7i_e4 = m7i_e3 := by
  ext i
  fin_cases i <;> decide

private theorem m7i_comb2 : (3 : ZMod 7) • m7i_u2 + m7i_e3 - m7i_e4 = m7i_e2 := by
  ext i
  fin_cases i <;> decide

private theorem m7i_comb1 :
    (3 : ZMod 7) • m7i_u1 + m7i_e2 - m7i_e3 - m7i_e4 = m7i_e1 := by
  ext i
  fin_cases i <;> decide

private theorem m7i_e4_mem (W : Submodule (ZMod 7) (Fin 4 → ZMod 7))
    (hJ : ∀ v ∈ W,
      Matrix.vecMul v !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] ∈ W)
    (hA : ∀ v ∈ W,
      Matrix.vecMul v !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5] ∈ W)
    (hne : W ≠ ⊥) : m7i_e4 ∈ W := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨v, hv, hv0⟩ := hne
  by_cases ha : v 0 = 0
  · by_cases hb : v 1 = 0
    · by_cases hc : v 2 = 0
      · have hv' : v = ![0, 0, 0, v 3] := by
          ext i
          fin_cases i <;> simp [ha, hb, hc]
        have hd : v 3 ≠ 0 := by
          intro h
          apply hv0
          rw [hv']
          simp [h]
        have hsm : (v 3)⁻¹ • v = m7i_e4 := by
          rw [hv']
          ext i
          fin_cases i <;> simp [m7i_e4, Pi.smul_apply, smul_eq_mul, hd, inv_mul_cancel₀ hd]
        rw [← hsm]
        exact Submodule.smul_mem W _ hv
      · have hN : m7i_N v = ![0, 0, 0, v 2] := by
          rw [m7i_N_eq v]
          ext i
          fin_cases i <;> simp [ha, hb]
        have hmem : m7i_N v ∈ W := m7i_N_mem hJ hv
        rw [hN] at hmem
        have hsm : (v 2)⁻¹ • ![0, 0, 0, v 2] = m7i_e4 := by
          ext i
          fin_cases i <;> simp [m7i_e4, Pi.smul_apply, smul_eq_mul, hc, inv_mul_cancel₀ hc]
        rw [← hsm]
        exact Submodule.smul_mem W _ hmem
    · have hNN : m7i_N (m7i_N v) = ![0, 0, 0, v 1] := by
        rw [m7i_NN v]
        ext i
        fin_cases i <;> simp [ha, hb]
      have hmem : m7i_N (m7i_N v) ∈ W := m7i_N_mem hJ (m7i_N_mem hJ hv)
      rw [hNN] at hmem
      have hsm : (v 1)⁻¹ • ![0, 0, 0, v 1] = m7i_e4 := by
        ext i
        fin_cases i <;> simp [m7i_e4, Pi.smul_apply, smul_eq_mul, hb, inv_mul_cancel₀ hb]
      rw [← hsm]
      exact Submodule.smul_mem W _ hmem
  · have hNNN : m7i_N (m7i_N (m7i_N v)) = ![0, 0, 0, v 0] := m7i_NNN v
    have hmem : m7i_N (m7i_N (m7i_N v)) ∈ W :=
      m7i_N_mem hJ (m7i_N_mem hJ (m7i_N_mem hJ hv))
    rw [hNNN] at hmem
    have hsm : (v 0)⁻¹ • ![0, 0, 0, v 0] = m7i_e4 := by
      ext i
      fin_cases i <;> simp [m7i_e4, Pi.smul_apply, smul_eq_mul, ha, inv_mul_cancel₀ ha]
    rw [← hsm]
    exact Submodule.smul_mem W _ hmem

private theorem m7i_top_of_e4 (W : Submodule (ZMod 7) (Fin 4 → ZMod 7))
    (hJ : ∀ v ∈ W,
      Matrix.vecMul v !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] ∈ W)
    (hA : ∀ v ∈ W,
      Matrix.vecMul v !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5] ∈ W)
    (he4 : m7i_e4 ∈ W) : W = ⊤ := by
  have hu1 : m7i_u1 ∈ W := by
    have h := hA m7i_e4 he4
    rwa [m7i_e4B] at h
  have hu2 : m7i_u2 ∈ W := by
    have h := m7i_N_mem hJ hu1
    rwa [m7i_u1N] at h
  have hu3 : m7i_u3 ∈ W := by
    have h := m7i_N_mem hJ hu2
    rwa [m7i_u2N] at h
  have hu4 : m7i_u4 ∈ W := by
    have h := m7i_N_mem hJ hu3
    rwa [m7i_u3N] at h
  have he3 : m7i_e3 ∈ W := by
    have h : (3 : ZMod 7) • m7i_u3 + m7i_e4 ∈ W :=
      Submodule.add_mem W (Submodule.smul_mem W 3 hu3) he4
    rwa [m7i_comb3] at h
  have he2 : m7i_e2 ∈ W := by
    have h : (3 : ZMod 7) • m7i_u2 + m7i_e3 - m7i_e4 ∈ W :=
      Submodule.sub_mem W (Submodule.add_mem W (Submodule.smul_mem W 3 hu2) he3) he4
    rwa [m7i_comb2] at h
  have he1 : m7i_e1 ∈ W := by
    have h : (3 : ZMod 7) • m7i_u1 + m7i_e2 - m7i_e3 - m7i_e4 ∈ W :=
      Submodule.sub_mem W
        (Submodule.sub_mem W (Submodule.add_mem W (Submodule.smul_mem W 3 hu1) he2) he3) he4
    rwa [m7i_comb1] at h
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = x 0 • m7i_e1 + x 1 • m7i_e2 + x 2 • m7i_e3 + x 3 • m7i_e4 := by
    ext i
    fin_cases i <;> simp [m7i_e1, m7i_e2, m7i_e3, m7i_e4]
  rw [hx]
  exact Submodule.add_mem W
    (Submodule.add_mem W
      (Submodule.add_mem W (Submodule.smul_mem W _ he1) (Submodule.smul_mem W _ he2))
      (Submodule.smul_mem W _ he3))
    (Submodule.smul_mem W _ he4)

theorem m7_quot_irreducible (W : Submodule (ZMod 7) (Fin 4 → ZMod 7))
    (hJ : ∀ v ∈ W, Matrix.vecMul v !![1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] ∈ W)
    (hA : ∀ v ∈ W, Matrix.vecMul v !![3, 4, 3, 0; 2, 6, 1, 4; 5, 2, 6, 3; 5, 2, 5, 5] ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  · exact Or.inr (m7i_top_of_e4 W hJ hA (m7i_e4_mem W hJ hA h))

end CFSG.StandardType.SporadicShape
