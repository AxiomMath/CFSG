module

public import CFSG.Open.StatedAPI
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

abbrev Idx : Type := Fin 4 ⊕ Fin 4

abbrev Vec : Type := Idx → ZMod 2

abbrev Jm : Matrix Idx Idx (ZMod 2) := fromBlocks 0 1 (-1) 0

@[expose] def omega (u v : Vec) : ZMod 2 := u ⬝ᵥ (Jm *ᵥ v)

@[expose] def Q0 : Vec → ZMod 2 := StatedQuadPlus 4 (ZMod 2)

@[expose] def idx : Idx → ℕ := Sum.elim (fun k => k.val) (fun k => 4 + k.val)

@[expose] def matOf (rows : List (List ℕ)) : Matrix Idx Idx (ZMod 2) :=
  Matrix.of fun i j => ((rows.getD (idx i) []).getD (idx j) 0 : ℕ)

@[expose] def aStdM : Matrix Idx Idx (ZMod 2) :=
  matOf [[1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 1]]

@[expose] def bStdM : Matrix Idx Idx (ZMod 2) :=
  matOf [[0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1]]

@[expose] def hM : Matrix Idx Idx (ZMod 2) :=
  matOf [[1, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 1], [1, 1, 0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 1]]

@[expose] def hInvM : Matrix Idx Idx (ZMod 2) :=
  matOf [[0, 1, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1],
    [0, 0, 1, 1, 0, 0, 0, 1], [1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 1, 0]]

@[expose] def a2M : Matrix Idx Idx (ZMod 2) :=
  matOf [[1, 1, 0, 0, 1, 1, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1, 0]]

@[expose] def b2M : Matrix Idx Idx (ZMod 2) :=
  matOf [[0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 1, 0, 0], [1, 1, 0, 0, 1, 1, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0, 0, 0, 1]]

@[expose] def aStd : GL Idx (ZMod 2) :=
  ⟨aStdM, aStdM * aStdM, by decide +kernel, by decide +kernel⟩

@[expose] def bStd : GL Idx (ZMod 2) :=
  ⟨bStdM, bStdM * bStdM, by decide +kernel, by decide +kernel⟩

@[expose] def hGL : GL Idx (ZMod 2) :=
  ⟨hM, hInvM, by decide +kernel, by decide +kernel⟩

@[expose] def a2 : GL Idx (ZMod 2) := hGL * aStd * hGL⁻¹

@[expose] def b2 : GL Idx (ZMod 2) := hGL * bStd * hGL⁻¹

@[expose] def E2 : Subgroup (GL Idx (ZMod 2)) := Subgroup.closure {a2, b2}

theorem coe_a2 : (a2 : Matrix Idx Idx (ZMod 2)) = a2M := by
  simp only [a2, Units.val_mul]
  decide +kernel

theorem coe_b2 : (b2 : Matrix Idx Idx (ZMod 2)) = b2M := by
  simp only [b2, Units.val_mul]
  decide +kernel

@[expose] def D0 (E : Subgroup (GL Idx (ZMod 2))) : Subgroup (GL Idx (ZMod 2)) :=
  Subgroup.closure {g | g ∈ StatedSp 4 (ZMod 2) ∧ ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}

@[expose] def tvM (w : Vec) : Matrix Idx Idx (ZMod 2) :=
  1 + Matrix.vecMulVec w (fun j => omega (Pi.single j 1) w)

theorem Jm_mulVec (v : Vec) :
    Jm *ᵥ v = Sum.elim (fun k => v (.inr k)) (fun k => v (.inl k)) := by
  simp only [Jm]
  rw [fromBlocks_mulVec]
  ext (i | i)
  · simp [Matrix.zero_mulVec, Matrix.one_mulVec]
  · simp only [Sum.elim_inr, Pi.add_apply, Matrix.zero_mulVec, Pi.zero_apply, zero_add,
      show (-1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 from CharTwo.neg_eq 1,
      Matrix.one_mulVec, Function.comp_apply, add_zero]

theorem omega_coord (u v : Vec) :
    omega u v = ∑ k : Fin 4, (u (.inl k) * v (.inr k) + u (.inr k) * v (.inl k)) := by
  rw [omega, dotProduct, Jm_mulVec, Fintype.sum_sum_type, Finset.sum_add_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr]

theorem omega_single_inl (k : Fin 4) (w : Vec) : omega (Pi.single (.inl k) 1) w = w (.inr k) := by
  rw [omega_coord, Fintype.sum_eq_single k (fun j hj => by simp [Pi.single_apply, hj])]
  simp

theorem omega_single_inr (k : Fin 4) (w : Vec) : omega (Pi.single (.inr k) 1) w = w (.inl k) := by
  rw [omega_coord, Fintype.sum_eq_single k (fun j hj => by simp [Pi.single_apply, hj])]
  simp

theorem omega_add_left (u u' v : Vec) : omega (u + u') v = omega u v + omega u' v := by
  show (u + u') ⬝ᵥ (Jm *ᵥ v) = u ⬝ᵥ (Jm *ᵥ v) + u' ⬝ᵥ (Jm *ᵥ v)
  rw [add_dotProduct]

theorem omega_add_right (u v v' : Vec) : omega u (v + v') = omega u v + omega u v' := by
  show u ⬝ᵥ (Jm *ᵥ (v + v')) = u ⬝ᵥ (Jm *ᵥ v) + u ⬝ᵥ (Jm *ᵥ v')
  rw [mulVec_add, dotProduct_add]

theorem omega_comm (u v : Vec) : omega u v = omega v u := by
  rw [omega_coord, omega_coord]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem omega_self (v : Vec) : omega v v = 0 := by
  rw [omega_coord]
  apply Finset.sum_eq_zero
  intro k _
  rw [mul_comm (v (.inr k)) (v (.inl k))]
  exact CharTwo.add_self_eq_zero _

theorem eq_zero_of_omega_eq_zero {v : Vec} (h : ∀ u, omega v u = 0) : v = 0 := by
  funext i
  rcases i with k | k
  · have h1 := h (Pi.single (.inr k) 1)
    rw [omega_coord, Fintype.sum_eq_single k (fun j hj => by simp [Pi.single_apply, hj])] at h1
    simpa using h1
  · have h1 := h (Pi.single (.inl k) 1)
    rw [omega_coord, Fintype.sum_eq_single k (fun j hj => by simp [Pi.single_apply, hj])] at h1
    simpa using h1

theorem omega_eq_sum (u v : Vec) :
    omega u v = ∑ k : Fin 4, (u (.inl k) * v (.inr k) + u (.inr k) * v (.inl k)) :=
  omega_coord u v

theorem Q0_eq_sum (v : Vec) : Q0 v = ∑ k : Fin 4, v (.inl k) * v (.inr k) := by
  simp only [Q0, StatedQuadPlus, CFSG.MatrixModel.plusQuadCore]

theorem Q0_add (u v : Vec) : Q0 (u + v) = Q0 u + Q0 v + omega u v := by
  have hR : Q0 u + Q0 v + omega u v =
      ∑ k : Fin 4, (u (.inl k) + v (.inl k)) * (u (.inr k) + v (.inr k)) := by
    rw [Q0_eq_sum, Q0_eq_sum, omega_eq_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hR, Q0_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.add_apply]

theorem omega_mulVec_dotProduct_transpose (A : Matrix Idx Idx (ZMod 2)) (u w : Vec) :
    (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm]
  exact (dotProduct_transpose_mulVec A u w).symm

theorem mem_statedSp_iff_omega (A : GL Idx (ZMod 2)) :
    A ∈ StatedSp 4 (ZMod 2) ↔
      ∀ u v : Vec, omega ((A : Matrix Idx Idx (ZMod 2)) *ᵥ u) ((A : Matrix Idx Idx (ZMod 2)) *ᵥ v) =
        omega u v := by
  constructor
  · intro hA u v
    have hJ : (A : Matrix Idx Idx (ZMod 2))ᵀ * Jm * (A : Matrix Idx Idx (ZMod 2)) = Jm :=
      (CFSG.Open.StatedAPI.mem_statedSp_iff).mp hA
    simp only [omega]
    rw [omega_mulVec_dotProduct_transpose (A : Matrix Idx Idx (ZMod 2)) u
      (Jm *ᵥ ((A : Matrix Idx Idx (ZMod 2)) *ᵥ v))]
    have hinner : (A : Matrix Idx Idx (ZMod 2))ᵀ *ᵥ
        (Jm *ᵥ ((A : Matrix Idx Idx (ZMod 2)) *ᵥ v)) = Jm *ᵥ v := by
      rw [mulVec_mulVec, mulVec_mulVec, hJ]
    rw [hinner]
  · intro h
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
    ext i j
    have h' := h (Pi.single i 1) (Pi.single j 1)
    simp only [omega] at h'
    rw [omega_mulVec_dotProduct_transpose] at h'
    rw [mulVec_mulVec, mulVec_mulVec] at h'
    rw [single_one_dotProduct, single_one_dotProduct] at h'
    rw [mulVec_single_one, mulVec_single_one] at h'
    exact h'

theorem matrixOrthogonal_le_statedSp : matrixOrthogonal Q0 ≤ StatedSp 4 (ZMod 2) := by
  intro A hA
  rw [mem_statedSp_iff_omega]
  intro u v
  have h1 := hA (u + v)
  rw [Matrix.mulVec_add, Q0_add, Q0_add, hA u, hA v] at h1
  exact add_left_cancel h1

theorem aStd_mem : aStd ∈ StatedSp 4 (ZMod 2) := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  decide +kernel

theorem bStd_mem : bStd ∈ StatedSp 4 (ZMod 2) := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  decide +kernel

theorem hGL_mem : hGL ∈ StatedSp 4 (ZMod 2) := by
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
  decide +kernel

theorem aStd_comm_bStd : aStd * bStd = bStd * aStd := by
  apply Units.ext
  decide +kernel

theorem aStd_pow_three : aStd ^ 3 = 1 := by
  apply Units.ext
  decide +kernel

theorem bStd_pow_three : bStd ^ 3 = 1 := by
  apply Units.ext
  decide +kernel

theorem omega_smul_coefficient (c : ZMod 2) (v w : Vec) : omega (c • v) w = c * omega v w := by
  rw [omega_coord, omega_coord, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem vecMulVec_mulVec_coord (w c x : Vec) :
    Matrix.vecMulVec w c *ᵥ x = (c ⬝ᵥ x) • w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tvCoeff_inl (w x : Vec) :
    (∑ k : Fin 4, omega (Pi.single (.inl k) 1) w * x (.inl k)) =
      ∑ k : Fin 4, x (.inl k) * w (.inr k) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [omega_single_inl]
  ring

theorem tvCoeff_inr (w x : Vec) :
    (∑ k : Fin 4, omega (Pi.single (.inr k) 1) w * x (.inr k)) =
      ∑ k : Fin 4, x (.inr k) * w (.inl k) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [omega_single_inr]
  ring

theorem tvCoeff_dotProduct (w x : Vec) :
    (fun j => omega (Pi.single j 1) w) ⬝ᵥ x = omega x w := by
  simp only [dotProduct]
  rw [omega_coord, Fintype.sum_sum_type, Finset.sum_add_distrib, tvCoeff_inl, tvCoeff_inr]

theorem tvM_mulVec (w x : Vec) : tvM w *ᵥ x = x + omega x w • w := by
  simp only [tvM, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [vecMulVec_mulVec_coord, tvCoeff_dotProduct]

theorem tvM_mul_self (w : Vec) : tvM w * tvM w = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, tvM_mulVec, tvM_mulVec, Matrix.one_mulVec]
  rw [omega_add_left, omega_smul_coefficient, omega_self, mul_zero, add_zero]
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

@[expose] def tvGL (w : Vec) : GL Idx (ZMod 2) :=
  ⟨tvM w, tvM w, tvM_mul_self w, tvM_mul_self w⟩

end CFSG.StandardType.SpEight
