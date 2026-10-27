module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.BlockSuccRankOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem isUnit_det_of_mul_self' {n : ℕ} {K : Type} [Field K]
    (M : Matrix (Fin n) (Fin n) K) (h : M * M = 1) : IsUnit M.det :=
  isUnit_iff_exists.mpr ⟨M.det, by rw [← Matrix.det_mul, h, Matrix.det_one],
    by rw [← Matrix.det_mul, h, Matrix.det_one]⟩

private theorem isUnit_det_blockSucc_diagSign (i : Fin 4) :
    IsUnit (Matrix.blockSucc (diagSignMat i) : Matrix (Fin 5) (Fin 5) (ZMod p)).det := by
  rw [Matrix.det_blockSucc]
  rw [show (diagSignMat i : Matrix (Fin 4) (Fin 4) (ZMod p)).det = -1 by
    rw [show (diagSignMat i : Matrix (Fin 4) (Fin 4) (ZMod p)) =
      Matrix.diagonal (fun j => if j = i then -1 else 1) from rfl, Matrix.det_diagonal]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi]
  exact isUnit_neg_one

private theorem isUnit_det_blockSucc_pij01 :
    IsUnit (Matrix.blockSucc (pijMat (0 : Fin 4) 1 (1 : ZMod p)) :
      Matrix (Fin 5) (Fin 5) (ZMod p)).det := by
  rw [Matrix.det_blockSucc]
  refine isUnit_det_of_mul_self' _ ?_
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem isUnit_det_blockSucc_pij12 :
    IsUnit (Matrix.blockSucc (pijMat (1 : Fin 4) 2 (1 : ZMod p)) :
      Matrix (Fin 5) (Fin 5) (ZMod p)).det := by
  rw [Matrix.det_blockSucc]
  refine isUnit_det_of_mul_self' _ ?_
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem isUnit_det_blockSucc_halfOnes (hp2 : p ≠ 2) :
    IsUnit (Matrix.blockSucc (halfOnesMat 4) : Matrix (Fin 5) (Fin 5) (ZMod p)).det := by
  rw [Matrix.det_blockSucc]
  refine isUnit_det_of_mul_self' _ ?_
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [halfOnesMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]
  all_goals
    have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
    have h4ne : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]
      exact mul_ne_zero h2ne h2ne
    field_simp [h2ne, h4ne]
    ring

private theorem p01_d0_p01 :
    (pijMat (0 : Fin 4) 1 (1 : ZMod p) * diagSignMat (0 : Fin 4)) *
      pijMat (0 : Fin 4) 1 1 = diagSignMat (1 : Fin 4) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem d0_p01_d0 :
    (diagSignMat (0 : Fin 4) * pijMat (0 : Fin 4) 1 (1 : ZMod p)) *
      diagSignMat (0 : Fin 4) = pijMat (0 : Fin 4) 1 (-1 : ZMod p) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem a4_p01m_a4 (hp2 : p ≠ 2) :
    ((((halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)) * diagSignMat (0 : Fin 4)) *
      pijMat (0 : Fin 4) 1 1) * diagSignMat (0 : Fin 4)) * halfOnesMat 4 =
      pijMat (2 : Fin 4) 3 (-1 : ZMod p) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, halfOnesMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals
    have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
    have h4ne : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]
      exact mul_ne_zero h2ne h2ne
    field_simp [h2ne, h4ne]
    ring

private theorem p12_d1_p12 :
    (pijMat (1 : Fin 4) 2 (1 : ZMod p) * diagSignMat (1 : Fin 4)) *
      pijMat (1 : Fin 4) 2 1 = diagSignMat (2 : Fin 4) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem d2_p23m_d2 :
    (diagSignMat (2 : Fin 4) * pijMat (2 : Fin 4) 3 (-1 : ZMod p)) *
      diagSignMat (2 : Fin 4) = pijMat (2 : Fin 4) 3 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem p23_d2_p23 :
    (pijMat (2 : Fin 4) 3 (1 : ZMod p) * diagSignMat (2 : Fin 4)) *
      pijMat (2 : Fin 4) 3 1 = diagSignMat (3 : Fin 4) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem p12_p01_p12 :
    (pijMat (1 : Fin 4) 2 (1 : ZMod p) * pijMat (0 : Fin 4) 1 1) *
      pijMat (1 : Fin 4) 2 1 = pijMat (0 : Fin 4) 2 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem p23_p02_p23 :
    (pijMat (2 : Fin 4) 3 (1 : ZMod p) * pijMat (0 : Fin 4) 2 1) *
      pijMat (2 : Fin 4) 3 1 = pijMat (0 : Fin 4) 3 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem p23_p12_p23 :
    (pijMat (2 : Fin 4) 3 (1 : ZMod p) * pijMat (1 : Fin 4) 2 1) *
      pijMat (2 : Fin 4) 3 1 = pijMat (1 : Fin 4) 3 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem d1_p12_d1 :
    (diagSignMat (1 : Fin 4) * pijMat (1 : Fin 4) 2 (1 : ZMod p)) *
      diagSignMat (1 : Fin 4) = pijMat (1 : Fin 4) 2 (-1 : ZMod p) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem d0_p02_d0 :
    (diagSignMat (0 : Fin 4) * pijMat (0 : Fin 4) 2 (1 : ZMod p)) *
      diagSignMat (0 : Fin 4) = pijMat (0 : Fin 4) 2 (-1 : ZMod p) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem d0_p03_d0 :
    (diagSignMat (0 : Fin 4) * pijMat (0 : Fin 4) 3 (1 : ZMod p)) *
      diagSignMat (0 : Fin 4) = pijMat (0 : Fin 4) 3 (-1 : ZMod p) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem d1_p13_d1 :
    (diagSignMat (1 : Fin 4) * pijMat (1 : Fin 4) 3 (1 : ZMod p)) *
      diagSignMat (1 : Fin 4) = pijMat (1 : Fin 4) 3 (-1 : ZMod p) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pijMat, diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem memF4_gen (f : Module.Basis (Fin 5) (ZMod p) U)
    {N : Matrix (Fin 4) (Fin 4) (ZMod p)} (hdet : IsUnit (Matrix.blockSucc N).det)
    (hN : N ∈ weylF4Mats := by simp [weylF4Mats]) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc N :=
  exists_mem_basisClosure_toMatrix_eq f (S := f4ExtMats) (M := Matrix.blockSucc N)
    (Set.mem_image_of_mem Matrix.blockSucc hN) hdet

private theorem memF4_gD0 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (diagSignMat (0 : Fin 4)) :=
  memF4_gen f (N := diagSignMat (0 : Fin 4)) (isUnit_det_blockSucc_diagSign 0)

private theorem memF4_gP01 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (0 : Fin 4) 1 (1 : ZMod p)) :=
  memF4_gen f (N := pijMat (0 : Fin 4) 1 (1 : ZMod p)) isUnit_det_blockSucc_pij01

private theorem memF4_gP12 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (1 : Fin 4) 2 (1 : ZMod p)) :=
  memF4_gen f (N := pijMat (1 : Fin 4) 2 (1 : ZMod p)) isUnit_det_blockSucc_pij12

private theorem memF4_mul {f : Module.Basis (Fin 5) (ZMod p) U}
    {A B : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hA : ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc A)
    (hB : ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc B) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (A * B) := by
  obtain ⟨gA, hgA, hA⟩ := hA
  obtain ⟨gB, hgB, hB⟩ := hB
  refine ⟨gA * gB, (basisClosure f f4ExtMats).mul_mem hgA hgB, ?_⟩
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hA, hB, Matrix.blockSucc_mul]

private theorem toFin5_diag {f : Module.Basis (Fin 5) (ZMod p) U} {k : Fin 4} {i : Fin 5}
    (hi : Fin.castSucc k = i) {g : U ≃ₗ[ZMod p] U}
    (h : LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (diagSignMat k)) :
    LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i := by
  rw [h, blockSucc_diagSignMat, hi]

private theorem toFin5_pij {f : Module.Basis (Fin 5) (ZMod p) U} {i j : Fin 4} {i' j' : Fin 5}
    (hi : Fin.castSucc i = i') (hj : Fin.castSucc j = j') (s : ZMod p) {g : U ≃ₗ[ZMod p] U}
    (h : LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (pijMat i j s)) :
    LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i' j' s := by
  rw [h, blockSucc_pijMat, hi, hj]

private theorem memF4_a4 (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (halfOnesMat 4) :=
  memF4_gen f (N := halfOnesMat 4) (isUnit_det_blockSucc_halfOnes hp2)
private theorem memF4_d1b (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (diagSignMat (1 : Fin 4)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_gP01 f) (memF4_gD0 f)) (memF4_gP01 f)
  refine ⟨g, hg, ?_⟩
  rwa [p01_d0_p01] at hgm
private theorem memF4_p01mb (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (0 : Fin 4) 1 (-1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_gD0 f) (memF4_gP01 f)) (memF4_gD0 f)
  refine ⟨g, hg, ?_⟩
  rwa [d0_p01_d0] at hgm
private theorem memF4_p23mb (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (2 : Fin 4) 3 (-1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ :=
    memF4_mul (memF4_mul (memF4_mul (memF4_mul (memF4_a4 f hp2) (memF4_gD0 f))
      (memF4_gP01 f)) (memF4_gD0 f)) (memF4_a4 f hp2)
  refine ⟨g, hg, ?_⟩
  rwa [a4_p01m_a4 hp2] at hgm
private theorem memF4_d2b (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (diagSignMat (2 : Fin 4)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_gP12 f) (memF4_d1b f)) (memF4_gP12 f)
  refine ⟨g, hg, ?_⟩
  rwa [p12_d1_p12] at hgm
private theorem memF4_p23b (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (2 : Fin 4) 3 (1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_d2b f) (memF4_p23mb f hp2)) (memF4_d2b f)
  refine ⟨g, hg, ?_⟩
  rwa [d2_p23m_d2] at hgm
private theorem memF4_d3b (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (diagSignMat (3 : Fin 4)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_p23b f hp2) (memF4_d2b f)) (memF4_p23b f hp2)
  refine ⟨g, hg, ?_⟩
  rwa [p23_d2_p23] at hgm
private theorem memF4_p12mb (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (1 : Fin 4) 2 (-1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_d1b f) (memF4_gP12 f)) (memF4_d1b f)
  refine ⟨g, hg, ?_⟩
  rwa [d1_p12_d1] at hgm
private theorem memF4_p02b (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (0 : Fin 4) 2 (1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_gP12 f) (memF4_gP01 f)) (memF4_gP12 f)
  refine ⟨g, hg, ?_⟩
  rwa [p12_p01_p12] at hgm
private theorem memF4_p02mb (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (0 : Fin 4) 2 (-1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_gD0 f) (memF4_p02b f)) (memF4_gD0 f)
  refine ⟨g, hg, ?_⟩
  rwa [d0_p02_d0] at hgm
private theorem memF4_p03b (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (0 : Fin 4) 3 (1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_p23b f hp2) (memF4_p02b f)) (memF4_p23b f hp2)
  refine ⟨g, hg, ?_⟩
  rwa [p23_p02_p23] at hgm
private theorem memF4_p03mb (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (0 : Fin 4) 3 (-1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_gD0 f) (memF4_p03b f hp2)) (memF4_gD0 f)
  refine ⟨g, hg, ?_⟩
  rwa [d0_p03_d0] at hgm
private theorem memF4_p13b (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (1 : Fin 4) 3 (1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_p23b f hp2) (memF4_gP12 f)) (memF4_p23b f hp2)
  refine ⟨g, hg, ?_⟩
  rwa [p23_p12_p23] at hgm
private theorem memF4_p13mb (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        Matrix.blockSucc (pijMat (1 : Fin 4) 3 (-1 : ZMod p)) := by
  obtain ⟨g, hg, hgm⟩ := memF4_mul (memF4_mul (memF4_d1b f) (memF4_p13b f hp2)) (memF4_d1b f)
  refine ⟨g, hg, ?_⟩
  rwa [d1_p13_d1] at hgm
private theorem memF4_d0 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (0 : Fin 5) := by
  obtain ⟨g, hg, hgm⟩ := memF4_gD0 f
  exact ⟨g, hg, toFin5_diag (Fin.ext rfl) hgm⟩
private theorem memF4_d1 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (1 : Fin 5) := by
  obtain ⟨g, hg, hgm⟩ := memF4_d1b f
  exact ⟨g, hg, toFin5_diag (Fin.ext rfl) hgm⟩
private theorem memF4_p01m (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 1 (-1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p01mb f
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (-1 : ZMod p) hgm⟩
private theorem memF4_d2 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (2 : Fin 5) := by
  obtain ⟨g, hg, hgm⟩ := memF4_d2b f
  exact ⟨g, hg, toFin5_diag (Fin.ext rfl) hgm⟩
private theorem memF4_p12m (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (1 : Fin 5) 2 (-1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p12mb f
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (-1 : ZMod p) hgm⟩
private theorem memF4_p02 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 2 (1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p02b f
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (1 : ZMod p) hgm⟩
private theorem memF4_p02m (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 2 (-1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p02mb f
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (-1 : ZMod p) hgm⟩
private theorem memF4_p23m (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (2 : Fin 5) 3 (-1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p23mb f hp2
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (-1 : ZMod p) hgm⟩
private theorem memF4_p23 (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (2 : Fin 5) 3 (1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p23b f hp2
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (1 : ZMod p) hgm⟩
private theorem memF4_d3 (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (3 : Fin 5) := by
  obtain ⟨g, hg, hgm⟩ := memF4_d3b f hp2
  exact ⟨g, hg, toFin5_diag (Fin.ext rfl) hgm⟩
private theorem memF4_p03 (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 3 (1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p03b f hp2
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (1 : ZMod p) hgm⟩
private theorem memF4_p03m (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 3 (-1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p03mb f hp2
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (-1 : ZMod p) hgm⟩
private theorem memF4_p13 (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (1 : Fin 5) 3 (1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p13b f hp2
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (1 : ZMod p) hgm⟩
private theorem memF4_p13m (f : Module.Basis (Fin 5) (ZMod p) U) (hp2 : p ≠ 2) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (1 : Fin 5) 3 (-1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_p13mb f hp2
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (-1 : ZMod p) hgm⟩
private theorem memF4_p01 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 1 (1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_gP01 f
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (1 : ZMod p) hgm⟩

private theorem memF4_p12 (f : Module.Basis (Fin 5) (ZMod p) U) :
    ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (1 : Fin 5) 2 (1 : ZMod p) := by
  obtain ⟨g, hg, hgm⟩ := memF4_gP12 f
  exact ⟨g, hg, toFin5_pij (Fin.ext rfl) (Fin.ext rfl) (1 : ZMod p) hgm⟩

private theorem halfOnesMat_four :
    (halfOnesMat 4 : Matrix (Fin 4) (Fin 4) (ZMod p)) =
      1 - Matrix.vecMulVec ![1, 1, 1, 1] ![1 / 2, 1 / 2, 1 / 2, 1 / 2] := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [halfOnesMat, Matrix.sub_apply]


theorem exists_mem_f4ExtMats (hp : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U) :
    (∀ i : Fin 5, i.val < 4 → ∃ g ∈ basisClosure f f4ExtMats,
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i) ∧
    (∀ i j : Fin 5, i < j → j.val < 4 → ∀ s : ZMod p, (s = 1 ∨ s = -1) →
      ∃ g ∈ basisClosure f f4ExtMats,
        LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat i j s) ∧
    ∃ g ∈ basisClosure f f4ExtMats, LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ![1, 1, 1, 1, 0] ![1 / 2, 1 / 2, 1 / 2, 1 / 2, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    fin_cases i
    · exact memF4_d0 f
    · exact memF4_d1 f
    · exact memF4_d2 f
    · exact memF4_d3 f hp
    · exact absurd hi (by decide)
  · intro i j hij hj s hs
    rcases hs with rfl | rfl
    · fin_cases i <;> fin_cases j <;>
        first
        | exact memF4_p02 f | exact memF4_p01 f | exact memF4_p12 f
        | exact memF4_p23 f hp | exact memF4_p03 f hp | exact memF4_p13 f hp
        | exact absurd hij (by decide) | exact absurd hj (by decide)
    · fin_cases i <;> fin_cases j <;>
        first
        | exact memF4_p02m f | exact memF4_p01m f | exact memF4_p12m f
        | exact memF4_p23m f hp | exact memF4_p03m f hp | exact memF4_p13m f hp
        | exact absurd hij (by decide) | exact absurd hj (by decide)
  · obtain ⟨g, hg, hgm⟩ := memF4_a4 f hp
    refine ⟨g, hg, ?_⟩
    rw [hgm, halfOnesMat_four, Matrix.blockSucc_one_sub_vecMulVec]
    ext i j
    fin_cases i <;> fin_cases j <;> simp


theorem false_of_f4Eta (hp3 : 3 < p) {ψ₁ ψ₂ ψ₃ w₁ w₂ w₃ : ZMod p}
    (h1 : (ψ₁ = 0 ∧ w₁ = 0) ∨ ψ₁ * w₁ = 1) (h2 : (ψ₂ = 0 ∧ w₂ = 0) ∨ ψ₂ * w₂ = 1)
    (h3 : (ψ₃ = 0 ∧ w₃ = 0) ∨ ψ₃ * w₃ = 1) (h12 : ψ₁ * w₂ + ψ₂ * w₁ = 0)
    (h13 : ψ₁ * w₃ + ψ₃ * w₁ = 0) (h23 : ψ₂ * w₃ + ψ₃ * w₂ = 0)
    (hsum : ψ₁ * w₁ + ψ₂ * w₂ + ψ₃ * w₃ ≠ 2) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0 ∨ w₃ ≠ 0)
    (ha : EtaOK 4 (ψ₁ + ψ₂ + ψ₃) ((w₁ + w₂ + w₃) / 2)) : False := by
  have hbond : (ψ₁ + ψ₂ + ψ₃) * ((w₁ + w₂ + w₃) / 2) =
      (ψ₁ * w₁ + ψ₂ * w₂ + ψ₃ * w₃) / 2 := by
    linear_combination (1 / 2 : ZMod p) * h12 + (1 / 2 : ZMod p) * h13 +
      (1 / 2 : ZMod p) * h23
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · obtain ⟨hψ1, hw1⟩ := h1; obtain ⟨hψ2, hw2⟩ := h2; obtain ⟨hψ3, hw3⟩ := h3
    rcases hw with h | h | h <;> simp_all
  · obtain ⟨hψ1, hw1⟩ := h1; obtain ⟨hψ2, hw2⟩ := h2
    refine not_etaOK_four_of_mul_eq_half hp3 ?_ ha
    rw [hbond, hψ1, hw1, hψ2, hw2, h3]; ring
  · obtain ⟨hψ1, hw1⟩ := h1; obtain ⟨hψ3, hw3⟩ := h3
    refine not_etaOK_four_of_mul_eq_half hp3 ?_ ha
    rw [hbond, hψ1, hw1, hψ3, hw3, h2]; ring
  · obtain ⟨hψ1, hw1⟩ := h1
    exact hsum (by rw [hψ1, hw1, h2, h3]; ring)
  · obtain ⟨hψ2, hw2⟩ := h2; obtain ⟨hψ3, hw3⟩ := h3
    refine not_etaOK_four_of_mul_eq_half hp3 ?_ ha
    rw [hbond, hψ2, hw2, hψ3, hw3, h1]; ring
  · obtain ⟨hψ2, hw2⟩ := h2
    exact hsum (by rw [hψ2, hw2, h1, h3]; ring)
  · obtain ⟨hψ3, hw3⟩ := h3
    exact hsum (by rw [hψ3, hw3, h1, h2]; ring)
  · refine not_etaOK_four_of_mul_eq_three_halves hp3 ?_ ha
    rw [hbond, h1, h2, h3]; ring

variable {U : Type} [AddCommGroup U] [Module (ZMod p) U]


theorem false_of_coords_f4 (hp4 : 4 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) (f : Module.Basis (Fin 5) (ZMod p) U)
    (hH : basisClosure f f4ExtMats ≤ G) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hb : Module.reflection hψ ∈ G) (hbH : Module.reflection hψ ∉ basisClosure f f4ExtMats)
    (hw0 : f.repr w 0 = 0) (hψ0 : ψ (f 0) = 0) (hw4 : f.repr w 4 ≠ 0) (hψ4 : ψ (f 4) ≠ 0)
    (hw : ∃ i : Fin 4, f.repr w i.castSucc ≠ 0) : False := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  obtain ⟨hi, hπ, ha4⟩ := exists_mem_f4ExtMats hp2 f
  obtain ⟨gh1, hgh1, hhm1⟩ := hi 1 (by decide)
  obtain ⟨gh2, hgh2, hhm2⟩ := hi 2 (by decide)
  obtain ⟨gh3, hgh3, hhm3⟩ := hi 3 (by decide)
  obtain ⟨g01, hg01, hm01⟩ := hπ 0 1 (by decide) (by decide) 1 (Or.inl rfl)
  obtain ⟨g02, hg02, hm02⟩ := hπ 0 2 (by decide) (by decide) 1 (Or.inl rfl)
  obtain ⟨g03, hg03, hm03⟩ := hπ 0 3 (by decide) (by decide) 1 (Or.inl rfl)
  obtain ⟨g12, hg12, hm12⟩ := hπ 1 2 (by decide) (by decide) 1 (Or.inl rfl)
  obtain ⟨g13, hg13, hm13⟩ := hπ 1 3 (by decide) (by decide) 1 (Or.inl rfl)
  obtain ⟨g23, hg23, hm23⟩ := hπ 2 3 (by decide) (by decide) 1 (Or.inl rfl)
  obtain ⟨ga4, hga4, hma4⟩ := ha4
  have hbne : ∀ {g : U ≃ₗ[ZMod p] U}, g ∈ basisClosure f f4ExtMats →
      g ≠ Module.reflection hψ := fun hg heq => hbH (heq ▸ hg)
  have hd1 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (1 : Fin 5) :=
    ⟨gh1, hH hgh1, hbne hgh1, hhm1⟩
  have hd2 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (2 : Fin 5) :=
    ⟨gh2, hH hgh2, hbne hgh2, hhm2⟩
  have hd3 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat (3 : Fin 5) :=
    ⟨gh3, hH hgh3, hbne hgh3, hhm3⟩
  have hπ01 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 1 1 :=
    ⟨g01, hH hg01, hbne hg01, hm01⟩
  have hπ02 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 2 1 :=
    ⟨g02, hH hg02, hbne hg02, hm02⟩
  have hπ03 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (0 : Fin 5) 3 1 :=
    ⟨g03, hH hg03, hbne hg03, hm03⟩
  have hπ12 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (1 : Fin 5) 2 1 :=
    ⟨g12, hH hg12, hbne hg12, hm12⟩
  have hπ13 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (1 : Fin 5) 3 1 :=
    ⟨g13, hH hg13, hbne hg13, hm13⟩
  have hπ23 : ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = pijMat (2 : Fin 5) 3 1 :=
    ⟨g23, hH hg23, hbne hg23, hm23⟩
  have ht1 := repr_eq_zero_or_mul_eq_one_of_dMax_four hp4 hG f hψ hb
    (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide) hw0 hψ0 hd1 hπ01
  have ht2 := repr_eq_zero_or_mul_eq_one_of_dMax_four hp4 hG f hψ hb
    (i := (0 : Fin 5)) (j := (2 : Fin 5)) (by decide) hw0 hψ0 hd2 hπ02
  have ht3 := repr_eq_zero_or_mul_eq_one_of_dMax_four hp4 hG f hψ hb
    (i := (0 : Fin 5)) (j := (3 : Fin 5)) (by decide) hw0 hψ0 hd3 hπ03
  have hcross12 : ψ (f 1) * f.repr w 2 + ψ (f 2) * f.repr w 1 = 0 := by
    refine cross_eq_zero_of_dMax_four hp4 hG f hψ hb (i := (1 : Fin 5)) (j := (2 : Fin 5))
      (by decide) ht1 ht2 ?_
    intro s hs
    obtain ⟨g, hg, hgm⟩ := hπ 1 2 (by decide) (by decide) s hs
    exact ⟨g, hH hg, hbne hg, hgm⟩
  have hcross13 : ψ (f 1) * f.repr w 3 + ψ (f 3) * f.repr w 1 = 0 := by
    refine cross_eq_zero_of_dMax_four hp4 hG f hψ hb (i := (1 : Fin 5)) (j := (3 : Fin 5))
      (by decide) ht1 ht3 ?_
    intro s hs
    obtain ⟨g, hg, hgm⟩ := hπ 1 3 (by decide) (by decide) s hs
    exact ⟨g, hH hg, hbne hg, hgm⟩
  have hcross23 : ψ (f 2) * f.repr w 3 + ψ (f 3) * f.repr w 2 = 0 := by
    refine cross_eq_zero_of_dMax_four hp4 hG f hψ hb (i := (2 : Fin 5)) (j := (3 : Fin 5))
      (by decide) ht2 ht3 ?_
    intro s hs
    obtain ⟨g, hg, hgm⟩ := hπ 2 3 (by decide) (by decide) s hs
    exact ⟨g, hH hg, hbne hg, hgm⟩
  have hψsum : ψ w = ∑ i : Fin 5, ψ (f i) * f.repr w i := by
    have h := congrArg (fun φ : Module.Dual (ZMod p) U => φ w) (f.sum_dual_apply_smul_coord ψ)
    simpa [Module.Basis.coord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h.symm
  have hsum : ψ (f 1) * f.repr w 1 + ψ (f 2) * f.repr w 2 + ψ (f 3) * f.repr w 3 ≠ 2 := by
    intro hc
    have h4 : ψ (f 4) * f.repr w 4 = 0 := by
      have hw' := hψ
      rw [hψsum, Fin.sum_univ_five] at hw'
      simp only [hψ0, hw0, mul_zero, zero_add] at hw'
      linear_combination hw' - hc
    exact mul_ne_zero hψ4 hw4 h4
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hκρ : ∑ i : Fin 5, (![1 / 2, 1 / 2, 1 / 2, 1 / 2, 0] : Fin 5 → ZMod p) i *
      (![1, 1, 1, 1, 0] : Fin 5 → ZMod p) i = 2 := by
    rw [Fin.sum_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [h2ne]
    ring_nf
  have ha : EtaOK 4 (ψ (f 1) + ψ (f 2) + ψ (f 3))
      ((f.repr w 1 + f.repr w 2 + f.repr w 3) / 2) := by
    have h := etaOK_of_toMatrix hG (d := 4) (by norm_num) hp4 (by omega) f hb (hH hga4)
      (Ne.symm (hbne hga4)) hψ rfl hma4 hκρ
    have e1 : (∑ i : Fin 5, ψ (f i) * (![1, 1, 1, 1, 0] : Fin 5 → ZMod p) i)
        = ψ (f 1) + ψ (f 2) + ψ (f 3) := by
      rw [Fin.sum_univ_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hψ0, mul_zero,
        zero_mul, zero_add, add_zero]
      ring
    have e2 : (∑ i : Fin 5, (![1 / 2, 1 / 2, 1 / 2, 1 / 2, 0] : Fin 5 → ZMod p) i *
        f.repr w i) = (f.repr w 1 + f.repr w 2 + f.repr w 3) / 2 := by
      rw [Fin.sum_univ_five]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hw0, mul_zero,
        zero_mul, zero_add, add_zero]
      ring
    rw [e1, e2] at h
    exact h
  have hw' : f.repr w 1 ≠ 0 ∨ f.repr w 2 ≠ 0 ∨ f.repr w 3 ≠ 0 := by
    obtain ⟨i, hi⟩ := hw
    fin_cases i
    · exact absurd hw0 hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  exact false_of_f4Eta hp3 ht1 ht2 ht3 hcross12 hcross13 hcross23 hsum hw' ha



namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

theorem lemmaThreeSix (hp : p ≠ 2) (hp3 : p ≠ 3) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 4) (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hF : TFF4Model p) {f : Module.Basis (Fin 5) (ZMod p) U}
    (hfH : H = basisClosure f f4ExtMats) : False := by
  have hp4 : 4 < p := by
    have := Nat.Prime.five_le_of_ne_two_of_ne_three (Fact.out : p.Prime) hp hp3
    omega
  obtain ⟨hi, _, _⟩ := exists_mem_f4ExtMats hp f
  obtain ⟨g0, hg0, hm0⟩ := hi 0 (by decide)
  obtain ⟨g1, hg1, hm1⟩ := hi 1 (by decide)
  obtain ⟨g2, hg2, hm2⟩ := hi 2 (by decide)
  obtain ⟨g3, hg3, hm3⟩ := hi 3 (by decide)
  have hz : LinearMap.toMatrix f f ((g0 * g1 * g2 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      diagSignMat (0 : Fin 5) * diagSignMat (1 : Fin 5) * diagSignMat (2 : Fin 5) := by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul,
      LinearMap.toMatrix_mul, hm0, hm1, hm2]
  obtain ⟨w, ψ, hψ, hb, hbH, hw0, hψ0, hwlast, hψlast, hw⟩ :=
    exists_reflection_coords hp S hneg (m := 4) f (T := weylF4Mats) hfH hm0
      (hfH.symm ▸ hF (W := U) f hp hp3 g0 (g0 * g1 * g2) g3 hm0 hz hm3)
  exact false_of_coords_f4 hp4 S.dmax f (hfH ▸ S.H_le) hψ hb (hfH ▸ hbH) hw0 hψ0
    hwlast hψlast hw


end PrimExtSetting

end CFSG.StandardType.ZS

end
