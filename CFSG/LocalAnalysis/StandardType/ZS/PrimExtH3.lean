module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtH3Eta
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K]

@[expose] def h3ReflRoot (α : K) (j : Fin 8) : Fin 4 → K :=
  ![![0, 1, 0, 0], ![0, 0, 1, 0], ![-1, 1 + α, 1 + α, 0], ![1, 1 + α, -(1 + α), 0],
    ![1, α - 1, α - 1, 0], ![1, α - 1, 1 - α, 0], ![1, 1 - α, 1 + α, 0],
    ![1, 1 - α, -(1 + α), 0]] j

@[expose] def h3ReflCoroot (α : K) (j : Fin 8) : Fin 4 → K :=
  ![![0, 2, 0, 0], ![0, 0, 2, 0], ![α / 2 - 1, 1 / 2, 1 - α / 2, 0],
    ![1 - α / 2, 1 / 2, α / 2 - 1, 0], ![(1 + α) / 2, α / 2, (α - 1) / 2, 0],
    ![(1 + α) / 2, α / 2, (1 - α) / 2, 0], ![1 / 2, (1 - α) / 2, 1 / 2, 0],
    ![1 / 2, (1 - α) / 2, -(1 / 2), 0]] j

private theorem alphaP2 {α : K} (hα : α ^ 2 = α + 1) : α ^ 2 = α + 1 := hα

private theorem alphaP3 {α : K} (hα : α ^ 2 = α + 1) : α ^ 3 = 2 * α + 1 := by
  linear_combination (α + 1) * hα

private theorem alphaP4 {α : K} (hα : α ^ 2 = α + 1) : α ^ 4 = 3 * α + 2 := by
  linear_combination (α ^ 2 + α + 2) * hα

private theorem alphaP5 {α : K} (hα : α ^ 2 = α + 1) : α ^ 5 = 5 * α + 3 := by
  linear_combination (α ^ 3 + α ^ 2 + 2 * α + 3) * hα

private theorem alphaP6 {α : K} (hα : α ^ 2 = α + 1) : α ^ 6 = 8 * α + 5 := by
  linear_combination (α ^ 4 + α ^ 3 + 2 * α ^ 2 + 3 * α + 5) * hα

private theorem blockSucc_one_sub_vecMulVec {n : ℕ} (ρ κ : Fin n → K) :
    Matrix.blockSucc (1 - Matrix.vecMulVec ρ κ) =
      1 - Matrix.vecMulVec (Fin.snoc ρ 0) (Fin.snoc κ 0) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.vecMulVec]
    | cast j =>
      simp [Matrix.vecMulVec, Matrix.one_apply]
      exact fun h => Fin.castSucc_ne_last j h.symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.vecMulVec]
    | cast j => simp [Matrix.vecMulVec, Matrix.one_apply]

private theorem h4BlockMat_eq_h4CandMat_0 (h2 : (2 : K) ≠ 0) {α : K} (hα : α ^ 2 = α + 1) :
    h4BlockMat α = h4CandMat α 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h4BlockMat, h4CandMat, h4CandRoot, h4CandCoroot, Matrix.vecMulVec,
      Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] <;>
    simp <;> (try field_simp) <;> (try ring_nf) <;>
    (try simp only [alphaP2 hα]) <;> ring

private theorem h4BlockMat_eq_h4CandMat_1 (h2 : (2 : K) ≠ 0) {α : K} (hα : α ^ 2 = α + 1) :
    h4BlockMat α = h4CandMat α 1 * diagSignMat 1 * h4CandMat α 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h4BlockMat, h4CandMat, h4CandRoot, h4CandCoroot, diagSignMat, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four] <;>
    simp <;> (try field_simp) <;> (try ring_nf) <;>
    (try simp only [alphaP4 hα, alphaP3 hα, alphaP2 hα]) <;> ring

private theorem h4BlockMat_eq_h4CandMat_2 (h2 : (2 : K) ≠ 0) {α : K} (hα : α ^ 2 = α + 1) :
    h4BlockMat α = h4CandMat α 2 * (diagSignMat 1 * diagSignMat 2) * h4CandMat α 2 *
        (diagSignMat 1 * diagSignMat 2) * h4CandMat α 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h4BlockMat, h4CandMat, h4CandRoot, h4CandCoroot, diagSignMat, Matrix.vecMulVec,
      Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_four] <;>
    simp <;> (try field_simp) <;> (try ring_nf) <;>
    (try simp only [alphaP6 hα, alphaP5 hα, alphaP4 hα, alphaP3 hα, alphaP2 hα]) <;> ring

theorem h4BlockMat_eq_h4CandMat (h2 : (2 : K) ≠ 0) {α : K} (hα : α ^ 2 = α + 1) :
    h4BlockMat α = h4CandMat α 0 ∧
      h4BlockMat α = h4CandMat α 1 * diagSignMat 1 * h4CandMat α 1 ∧
      h4BlockMat α = h4CandMat α 2 * (diagSignMat 1 * diagSignMat 2) * h4CandMat α 2 *
        (diagSignMat 1 * diagSignMat 2) * h4CandMat α 2 :=
  ⟨h4BlockMat_eq_h4CandMat_0 h2 hα, h4BlockMat_eq_h4CandMat_1 h2 hα,
    h4BlockMat_eq_h4CandMat_2 h2 hα⟩

end Matrices

section Basis

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

private theorem blockSucc_commute_diagonal_update {m : ℕ} (μ : Kˣ)
    (M : Matrix (Fin m) (Fin m) K) :
    Matrix.diagonal (fun i =>
        ((Function.update 1 (Fin.last m) μ : Fin (m + 1) → Kˣ) i : K)) * Matrix.blockSucc M =
      Matrix.blockSucc M * Matrix.diagonal (fun i =>
        ((Function.update 1 (Fin.last m) μ : Fin (m + 1) → Kˣ) i : K)) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Function.update]
    | cast j => simp [Matrix.blockSucc_last_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.blockSucc_castSucc_last]
    | cast j => simp [Function.update]

private theorem toMatrix_unitsSMul_mul_diagonal {m : ℕ} (f : Module.Basis (Fin (m + 1)) K V)
    (w : Fin (m + 1) → Kˣ) (g : V ≃ₗ[K] V) :
    f.toMatrix (fun j => g (f.unitsSMul w j)) =
      LinearMap.toMatrix f f (g : V →ₗ[K] V) * f.toMatrix (f.unitsSMul w) := by
  ext i j
  simp only [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, Matrix.mul_apply]
  conv_lhs => rw [← f.sum_repr (f.unitsSMul w j)]
  rw [map_sum]
  simp only [map_smul]
  rw [map_sum]
  simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem toMatrix_unitsSMul_conj {m : ℕ} (f : Module.Basis (Fin (m + 1)) K V)
    (w : Fin (m + 1) → Kˣ) (g : V ≃ₗ[K] V) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) =
      (f.toMatrix (f.unitsSMul w))⁻¹ * LinearMap.toMatrix f f (g : V →ₗ[K] V) *
        f.toMatrix (f.unitsSMul w) := by
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) K := Matrix.diagonal fun i => (w i : K) with hDdef
  have hD : f.toMatrix (f.unitsSMul w) = D := by
    rw [hDdef]; exact f.toMatrix_unitsSMul w
  have hDinv : (f.unitsSMul w).toMatrix f = D⁻¹ := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip (b := f.unitsSMul w) (b' := f)
    rw [hD] at h
    exact (Matrix.inv_eq_left_inv h).symm
  have hDDinv : D * D⁻¹ = 1 := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip (b := f) (b' := f.unitsSMul w)
    rw [hD, hDinv] at h
    exact h
  have hDinvD : D⁻¹ * D = 1 := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip (b := f.unitsSMul w) (b' := f)
    rw [hDinv, hD] at h
    exact h
  have hto : (f.unitsSMul w).toMatrix (fun j => g (f.unitsSMul w j)) =
      LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) := by
    ext i j
    simp only [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    rfl
  have hA : D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) =
      f.toMatrix (fun j => g (f.unitsSMul w j)) := by
    rw [← hD, ← hto]
    exact Module.Basis.toMatrix_mul_toMatrix (b := f) (b' := f.unitsSMul w)
      (b'' := fun j => g (f.unitsSMul w j))
  have hB : f.toMatrix (fun j => g (f.unitsSMul w j)) =
      LinearMap.toMatrix f f (g : V →ₗ[K] V) * D := by
    rw [← hD]
    exact toMatrix_unitsSMul_mul_diagonal f w g
  have hDX : D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) =
      LinearMap.toMatrix f f (g : V →ₗ[K] V) * D := by rw [hA, hB]
  rw [hD] at ⊢
  calc LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) =
      D⁻¹ * (D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V)) := by
        rw [← mul_assoc, hDinvD, one_mul]
    _ = D⁻¹ * (LinearMap.toMatrix f f (g : V →ₗ[K] V) * D) := by rw [hDX]
    _ = D⁻¹ * LinearMap.toMatrix f f (g : V →ₗ[K] V) * D := by rw [mul_assoc]

private theorem unitsSMul_blockSucc_set_eq {m : ℕ} (f : Module.Basis (Fin (m + 1)) K V)
    (w : Fin (m + 1) → Kˣ) (T : Set (Matrix (Fin m) (Fin m) K))
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hcomm : ∀ M : Matrix (Fin m) (Fin m) K, D * Matrix.blockSucc M = Matrix.blockSucc M * D)
    (hDDinv : D * D⁻¹ = 1) (hDinvD : D⁻¹ * D = 1)
    (hDX : ∀ g : V ≃ₗ[K] V, D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
      (g : V →ₗ[K] V) = LinearMap.toMatrix f f (g : V →ₗ[K] V) * D) :
    {g : V ≃ₗ[K] V | LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
        (g : V →ₗ[K] V) ∈ Matrix.blockSucc '' T} =
      {g : V ≃ₗ[K] V | LinearMap.toMatrix f f (g : V →ₗ[K] V) ∈ Matrix.blockSucc '' T} := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨M, hM, hM'⟩
    refine ⟨M, hM, ?_⟩
    have h1 : Matrix.blockSucc M * D = LinearMap.toMatrix f f (g : V →ₗ[K] V) * D := by
      rw [← hcomm M, ← hDX g, hM']
    have h2 : Matrix.blockSucc M * D * D⁻¹ =
        LinearMap.toMatrix f f (g : V →ₗ[K] V) * D * D⁻¹ := by rw [h1]
    simpa only [mul_assoc, hDDinv, mul_one] using h2
  · rintro ⟨M, hM, hM'⟩
    refine ⟨M, hM, ?_⟩
    have h1 : D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) =
        D * Matrix.blockSucc M := by
      rw [hDX g, ← hM', hcomm M]
    have h2 : D⁻¹ * (D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
          (g : V →ₗ[K] V)) = D⁻¹ * (D * Matrix.blockSucc M) := by rw [h1]
    have h3 : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (g : V →ₗ[K] V) =
        Matrix.blockSucc M := by
      simpa only [← mul_assoc, hDinvD, one_mul] using h2
    exact h3.symm

theorem basisClosure_unitsSMul_blockSucc {m : ℕ} (f : Module.Basis (Fin (m + 1)) K V) (μ : Kˣ)
    (T : Set (Matrix (Fin m) (Fin m) K)) :
    basisClosure (f.unitsSMul (Function.update 1 (Fin.last m) μ)) (Matrix.blockSucc '' T) =
      basisClosure f (Matrix.blockSucc '' T) := by
  set w : Fin (m + 1) → Kˣ := Function.update 1 (Fin.last m) μ with hw
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) K := Matrix.diagonal fun i => (w i : K) with hDdef
  have hcomm : ∀ M : Matrix (Fin m) (Fin m) K,
      D * Matrix.blockSucc M = Matrix.blockSucc M * D := fun M => by
    rw [hDdef, hw]; exact blockSucc_commute_diagonal_update μ M
  have hD : f.toMatrix (f.unitsSMul w) = D := by
    rw [hDdef, hw]; exact f.toMatrix_unitsSMul w
  have hDinv : (f.unitsSMul w).toMatrix f = D⁻¹ := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip (b := f.unitsSMul w) (b' := f)
    rw [hD] at h
    exact (Matrix.inv_eq_left_inv h).symm
  have hDDinv : D * D⁻¹ = 1 := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip (b := f) (b' := f.unitsSMul w)
    rw [hD, hDinv] at h
    exact h
  have hDinvD : D⁻¹ * D = 1 := by
    have h := Module.Basis.toMatrix_mul_toMatrix_flip (b := f.unitsSMul w) (b' := f)
    rw [hDinv, hD] at h
    exact h
  have hconj : ∀ g : V ≃ₗ[K] V, LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
      (g : V →ₗ[K] V) = D⁻¹ * LinearMap.toMatrix f f (g : V →ₗ[K] V) * D := by
    intro g
    have h := toMatrix_unitsSMul_conj f w g
    rwa [hD] at h
  have hDX : ∀ g : V ≃ₗ[K] V, D * LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w)
      (g : V →ₗ[K] V) = LinearMap.toMatrix f f (g : V →ₗ[K] V) * D := by
    intro g
    rw [hconj g]
    simp only [← mul_assoc, hDDinv, one_mul]
  exact congrArg Subgroup.closure (unitsSMul_blockSucc_set_eq f w T D hcomm hDDinv hDinvD hDX)


end Basis

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem h3ReflMat_0 {α : ZMod p} :
    diagSignMat (1 : Fin 4) = 1 - Matrix.vecMulVec (h3ReflRoot α 0) (h3ReflCoroot α 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [h3ReflRoot, h3ReflCoroot, diagSignMat, Matrix.vecMulVec]

private theorem h3ReflMat_1 {α : ZMod p} :
    diagSignMat (2 : Fin 4) = 1 - Matrix.vecMulVec (h3ReflRoot α 1) (h3ReflCoroot α 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [h3ReflRoot, h3ReflCoroot, diagSignMat, Matrix.vecMulVec]

private theorem h3Mat3_2 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    h3BlockMat α =
      1 - Matrix.vecMulVec ![-1, 1 + α, 1 + α] ![α / 2 - 1, 1 / 2, 1 - α / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h3BlockMat, Matrix.vecMulVec, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply] <;>
    simp <;> (try field_simp) <;> (try ring_nf) <;> (try simp only [hα]) <;> (try ring)

private theorem h3Mat3_3 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    diagSignMat (1 : Fin 3) * h3BlockMat α * diagSignMat (1 : Fin 3) =
      1 - Matrix.vecMulVec ![1, 1 + α, -(1 + α)] ![1 - α / 2, 1 / 2, α / 2 - 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h3BlockMat, diagSignMat, Matrix.vecMulVec, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Fin.sum_univ_three] <;>
    simp <;> (try field_simp) <;> (try ring_nf) <;> (try simp only [hα]) <;> (try ring)

private theorem h3Mat3_4 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    h3BlockMat α * diagSignMat (0 : Fin 3) * h3BlockMat α =
      1 - Matrix.vecMulVec ![1, α - 1, α - 1] ![(1 + α) / 2, α / 2, (α - 1) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h3BlockMat, diagSignMat, Matrix.vecMulVec, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Fin.sum_univ_three] <;>
    simp <;> (try field_simp) <;> (try simp only [hα]) <;> (try ring_nf) <;>
    (try simp only [hα]) <;> (try ring)

private theorem h3Mat3_5 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    diagSignMat (2 : Fin 3) * h3BlockMat α * diagSignMat (0 : Fin 3) * h3BlockMat α *
        diagSignMat (2 : Fin 3) =
      1 - Matrix.vecMulVec ![1, α - 1, 1 - α] ![(1 + α) / 2, α / 2, (1 - α) / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h3BlockMat, diagSignMat, Matrix.vecMulVec, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Fin.sum_univ_three] <;>
    simp <;> (try field_simp) <;> (try simp only [hα]) <;> (try ring_nf) <;>
    (try simp only [hα]) <;> (try ring)

private theorem h3Mat3_6 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    diagSignMat (2 : Fin 3) * h3BlockMat α * diagSignMat (1 : Fin 3) * h3BlockMat α *
        diagSignMat (2 : Fin 3) =
      1 - Matrix.vecMulVec ![1, 1 - α, 1 + α] ![1 / 2, (1 - α) / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h3BlockMat, diagSignMat, Matrix.vecMulVec, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Fin.sum_univ_three] <;>
    simp <;> (try field_simp) <;> (try simp only [hα]) <;> (try ring_nf) <;>
    (try simp only [hα]) <;> (try ring)

private theorem h3Mat3_7 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    h3BlockMat α * diagSignMat (1 : Fin 3) * h3BlockMat α =
      1 - Matrix.vecMulVec ![1, 1 - α, -(1 + α)] ![1 / 2, (1 - α) / 2, -(1 / 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [h3BlockMat, diagSignMat, Matrix.vecMulVec, Matrix.mul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      Fin.sum_univ_three] <;>
    simp <;> (try field_simp) <;> (try simp only [hα]) <;> (try ring_nf) <;>
    (try simp only [hα]) <;> (try ring)

private theorem h3ReflMat_2 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    Matrix.blockSucc (h3BlockMat α) =
      1 - Matrix.vecMulVec (h3ReflRoot α 2) (h3ReflCoroot α 2) := by
  have hW : Matrix.blockSucc (h3BlockMat α) = Matrix.blockSucc (h3BlockMat α) := rfl
  have hr : h3ReflRoot α 2 = Fin.snoc ![-1, 1 + α, 1 + α] 0 := by
    ext i; fin_cases i <;> simp [h3ReflRoot]
  have hc : h3ReflCoroot α 2 = Fin.snoc ![α / 2 - 1, 1 / 2, 1 - α / 2] 0 := by
    ext i; fin_cases i <;> simp [h3ReflCoroot]
  rw [hW, h3Mat3_2 hα h2, hr, hc]
  exact blockSucc_one_sub_vecMulVec _ _

private theorem h3ReflMat_3 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    diagSignMat (1 : Fin 4) * Matrix.blockSucc (h3BlockMat α) * diagSignMat (1 : Fin 4) =
      1 - Matrix.vecMulVec (h3ReflRoot α 3) (h3ReflCoroot α 3) := by
  have hW : diagSignMat (1 : Fin 4) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (1 : Fin 4) =
      Matrix.blockSucc (diagSignMat (1 : Fin 3) * h3BlockMat α * diagSignMat (1 : Fin 3)) := by
    show diagSignMat (Fin.castSucc (1 : Fin 3)) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (Fin.castSucc (1 : Fin 3)) =
      Matrix.blockSucc (diagSignMat (1 : Fin 3) * h3BlockMat α * diagSignMat (1 : Fin 3))
    simp only [← blockSucc_diagSignMat (1 : Fin 3), ← Matrix.blockSucc_mul]
  have hr : h3ReflRoot α 3 = Fin.snoc ![1, 1 + α, -(1 + α)] 0 := by
    ext i; fin_cases i <;> simp [h3ReflRoot]
  have hc : h3ReflCoroot α 3 = Fin.snoc ![1 - α / 2, 1 / 2, α / 2 - 1] 0 := by
    ext i; fin_cases i <;> simp [h3ReflCoroot]
  rw [hW, h3Mat3_3 hα h2, hr, hc]
  exact blockSucc_one_sub_vecMulVec _ _

private theorem h3ReflMat_4 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    Matrix.blockSucc (h3BlockMat α) * diagSignMat (0 : Fin 4) * Matrix.blockSucc (h3BlockMat α) =
      1 - Matrix.vecMulVec (h3ReflRoot α 4) (h3ReflCoroot α 4) := by
  have hW : Matrix.blockSucc (h3BlockMat α) * diagSignMat (0 : Fin 4) *
        Matrix.blockSucc (h3BlockMat α) =
      Matrix.blockSucc (h3BlockMat α * diagSignMat (0 : Fin 3) * h3BlockMat α) := by
    show Matrix.blockSucc (h3BlockMat α) * diagSignMat (Fin.castSucc (0 : Fin 3)) *
        Matrix.blockSucc (h3BlockMat α) =
      Matrix.blockSucc (h3BlockMat α * diagSignMat (0 : Fin 3) * h3BlockMat α)
    simp only [← blockSucc_diagSignMat (0 : Fin 3), ← Matrix.blockSucc_mul]
  have hr : h3ReflRoot α 4 = Fin.snoc ![1, α - 1, α - 1] 0 := by
    ext i; fin_cases i <;> simp [h3ReflRoot]
  have hc : h3ReflCoroot α 4 = Fin.snoc ![(1 + α) / 2, α / 2, (α - 1) / 2] 0 := by
    ext i; fin_cases i <;> simp [h3ReflCoroot]
  rw [hW, h3Mat3_4 hα h2, hr, hc]
  exact blockSucc_one_sub_vecMulVec _ _

private theorem h3ReflMat_5 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    diagSignMat (2 : Fin 4) * Matrix.blockSucc (h3BlockMat α) * diagSignMat (0 : Fin 4) *
        Matrix.blockSucc (h3BlockMat α) * diagSignMat (2 : Fin 4) =
      1 - Matrix.vecMulVec (h3ReflRoot α 5) (h3ReflCoroot α 5) := by
  have hW : diagSignMat (2 : Fin 4) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (0 : Fin 4) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (2 : Fin 4) =
      Matrix.blockSucc (diagSignMat (2 : Fin 3) * h3BlockMat α * diagSignMat (0 : Fin 3) *
        h3BlockMat α * diagSignMat (2 : Fin 3)) := by
    show diagSignMat (Fin.castSucc (2 : Fin 3)) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (Fin.castSucc (0 : Fin 3)) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (Fin.castSucc (2 : Fin 3)) =
      Matrix.blockSucc (diagSignMat (2 : Fin 3) * h3BlockMat α * diagSignMat (0 : Fin 3) *
        h3BlockMat α * diagSignMat (2 : Fin 3))
    simp only [← blockSucc_diagSignMat (0 : Fin 3), ← blockSucc_diagSignMat (2 : Fin 3),
      ← Matrix.blockSucc_mul]
  have hr : h3ReflRoot α 5 = Fin.snoc ![1, α - 1, 1 - α] 0 := by
    ext i; fin_cases i <;> simp [h3ReflRoot]
  have hc : h3ReflCoroot α 5 = Fin.snoc ![(1 + α) / 2, α / 2, (1 - α) / 2] 0 := by
    ext i; fin_cases i <;> simp [h3ReflCoroot]
  rw [hW, h3Mat3_5 hα h2, hr, hc]
  exact blockSucc_one_sub_vecMulVec _ _

private theorem h3ReflMat_6 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    diagSignMat (2 : Fin 4) * Matrix.blockSucc (h3BlockMat α) * diagSignMat (1 : Fin 4) *
        Matrix.blockSucc (h3BlockMat α) * diagSignMat (2 : Fin 4) =
      1 - Matrix.vecMulVec (h3ReflRoot α 6) (h3ReflCoroot α 6) := by
  have hW : diagSignMat (2 : Fin 4) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (1 : Fin 4) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (2 : Fin 4) =
      Matrix.blockSucc (diagSignMat (2 : Fin 3) * h3BlockMat α * diagSignMat (1 : Fin 3) *
        h3BlockMat α * diagSignMat (2 : Fin 3)) := by
    show diagSignMat (Fin.castSucc (2 : Fin 3)) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (Fin.castSucc (1 : Fin 3)) * Matrix.blockSucc (h3BlockMat α) *
        diagSignMat (Fin.castSucc (2 : Fin 3)) =
      Matrix.blockSucc (diagSignMat (2 : Fin 3) * h3BlockMat α * diagSignMat (1 : Fin 3) *
        h3BlockMat α * diagSignMat (2 : Fin 3))
    simp only [← blockSucc_diagSignMat (1 : Fin 3), ← blockSucc_diagSignMat (2 : Fin 3),
      ← Matrix.blockSucc_mul]
  have hr : h3ReflRoot α 6 = Fin.snoc ![1, 1 - α, 1 + α] 0 := by
    ext i; fin_cases i <;> simp [h3ReflRoot]
  have hc : h3ReflCoroot α 6 = Fin.snoc ![1 / 2, (1 - α) / 2, 1 / 2] 0 := by
    ext i; fin_cases i <;> simp [h3ReflCoroot]
  rw [hW, h3Mat3_6 hα h2, hr, hc]
  exact blockSucc_one_sub_vecMulVec _ _

private theorem h3ReflMat_7 {α : ZMod p} (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0) :
    Matrix.blockSucc (h3BlockMat α) * diagSignMat (1 : Fin 4) * Matrix.blockSucc (h3BlockMat α) =
      1 - Matrix.vecMulVec (h3ReflRoot α 7) (h3ReflCoroot α 7) := by
  have hW : Matrix.blockSucc (h3BlockMat α) * diagSignMat (1 : Fin 4) *
        Matrix.blockSucc (h3BlockMat α) =
      Matrix.blockSucc (h3BlockMat α * diagSignMat (1 : Fin 3) * h3BlockMat α) := by
    show Matrix.blockSucc (h3BlockMat α) * diagSignMat (Fin.castSucc (1 : Fin 3)) *
        Matrix.blockSucc (h3BlockMat α) =
      Matrix.blockSucc (h3BlockMat α * diagSignMat (1 : Fin 3) * h3BlockMat α)
    simp only [← blockSucc_diagSignMat (1 : Fin 3), ← Matrix.blockSucc_mul]
  have hr : h3ReflRoot α 7 = Fin.snoc ![1, 1 - α, -(1 + α)] 0 := by
    ext i; fin_cases i <;> simp [h3ReflRoot]
  have hc : h3ReflCoroot α 7 = Fin.snoc ![1 / 2, (1 - α) / 2, -(1 / 2)] 0 := by
    ext i; fin_cases i <;> simp [h3ReflCoroot]
  rw [hW, h3Mat3_7 hα h2, hr, hc]
  exact blockSucc_one_sub_vecMulVec _ _


private theorem isUnit_diagSignMat_det_four (i : Fin 4) :
    IsUnit (diagSignMat i : Matrix (Fin 4) (Fin 4) (ZMod p)).det := by
  rw [show (diagSignMat i : Matrix (Fin 4) (Fin 4) (ZMod p)).det = -1 by
    simp [diagSignMat, Matrix.det_diagonal]]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

private theorem diagSignMat_mem_h3Mats_four (α : ZMod p) (i : Fin 3) :
    (diagSignMat (Fin.castSucc i) : Matrix (Fin 4) (Fin 4) (ZMod p)) ∈ h3Mats α := by
  refine ⟨diagSignMat i, ?_, ?_⟩
  · fin_cases i <;> simp [h3BlockMats]
  · rw [blockSucc_diagSignMat]

private theorem isUnit_blockSucc_h3BlockMat_det {α : ZMod p} (hα : α ^ 2 = α + 1)
    (h2 : (2 : ZMod p) ≠ 0) :
    IsUnit (Matrix.blockSucc (h3BlockMat α) : Matrix (Fin 4) (Fin 4) (ZMod p)).det := by
  rw [Matrix.det_blockSucc]
  rw [show (h3BlockMat α : Matrix (Fin 3) (Fin 3) (ZMod p)).det = -1 by
    simp [h3BlockMat, Matrix.det_fin_three]
    field_simp
    ring_nf
    rw [show α ^ 2 = α + 1 from hα]
    ring]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

private theorem blockSucc_h3BlockMat_mem_h3Mats (α : ZMod p) :
    (Matrix.blockSucc (h3BlockMat α) : Matrix (Fin 4) (Fin 4) (ZMod p)) ∈ h3Mats α :=
  ⟨h3BlockMat α, by simp [h3BlockMats], rfl⟩

private theorem toMatrix_mul_three (f : Module.Basis (Fin 4) (ZMod p) U)
    (a b c : U ≃ₗ[ZMod p] U) :
    LinearMap.toMatrix f f ((a * b * c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (b : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (c : U →ₗ[ZMod p] U) := by
  rw [show ((a * b * c : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (a : U →ₗ[ZMod p] U) * (b : U →ₗ[ZMod p] U) * (c : U →ₗ[ZMod p] U) from rfl]
  simp only [LinearMap.toMatrix_mul]

private theorem toMatrix_mul_five (f : Module.Basis (Fin 4) (ZMod p) U)
    (a b c d e : U ≃ₗ[ZMod p] U) :
    LinearMap.toMatrix f f ((a * b * c * d * e : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (b : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (c : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (d : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (e : U →ₗ[ZMod p] U) := by
  rw [show ((a * b * c * d * e : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (a : U →ₗ[ZMod p] U) * (b : U →ₗ[ZMod p] U) * (c : U →ₗ[ZMod p] U) *
        (d : U →ₗ[ZMod p] U) * (e : U →ₗ[ZMod p] U) from rfl]
  simp only [LinearMap.toMatrix_mul]

private theorem h3Mats_mul_mem {α : ZMod p} (f : Module.Basis (Fin 4) (ZMod p) U)
    {a b : U ≃ₗ[ZMod p] U} (ha : a ∈ basisClosure f (h3Mats α))
    (hb : b ∈ basisClosure f (h3Mats α)) : a * b ∈ basisClosure f (h3Mats α) :=
  (basisClosure f (h3Mats α)).mul_mem ha hb

private theorem h3Mats_refl_case {α : ZMod p} (f : Module.Basis (Fin 4) (ZMod p) U)
    (hα : α ^ 2 = α + 1) (h2 : (2 : ZMod p) ≠ 0)
    {g0 g1 g2 ga : U ≃ₗ[ZMod p] U}
    (hg0 : g0 ∈ basisClosure f (h3Mats α)) (hg1 : g1 ∈ basisClosure f (h3Mats α))
    (hg2 : g2 ∈ basisClosure f (h3Mats α)) (hga : ga ∈ basisClosure f (h3Mats α))
    (hg0m : LinearMap.toMatrix f f (g0 : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hg1m : LinearMap.toMatrix f f (g1 : U →ₗ[ZMod p] U) = diagSignMat 1)
    (hg2m : LinearMap.toMatrix f f (g2 : U →ₗ[ZMod p] U) = diagSignMat 2)
    (hgam : LinearMap.toMatrix f f (ga : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    (j : Fin 8) :
    ∃ g ∈ basisClosure f (h3Mats α), LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec (h3ReflRoot α j) (h3ReflCoroot α j) := by
  fin_cases j <;> simp only [Fin.reduceFinMk]
  · exact ⟨g1, hg1, by rw [hg1m]; exact h3ReflMat_0 (α := α)⟩
  · exact ⟨g2, hg2, by rw [hg2m]; exact h3ReflMat_1 (α := α)⟩
  · exact ⟨ga, hga, by rw [hgam]; exact h3ReflMat_2 hα h2⟩
  · refine ⟨g1 * ga * g1, h3Mats_mul_mem f (h3Mats_mul_mem f hg1 hga) hg1, ?_⟩
    rw [toMatrix_mul_three f g1 ga g1, hg1m, hgam]
    exact h3ReflMat_3 hα h2
  · refine ⟨ga * g0 * ga, h3Mats_mul_mem f (h3Mats_mul_mem f hga hg0) hga, ?_⟩
    rw [toMatrix_mul_three f ga g0 ga, hgam, hg0m]
    exact h3ReflMat_4 hα h2
  · refine ⟨g2 * ga * g0 * ga * g2, ?_, ?_⟩
    · exact h3Mats_mul_mem f (h3Mats_mul_mem f (h3Mats_mul_mem f
        (h3Mats_mul_mem f hg2 hga) hg0) hga) hg2
    · rw [toMatrix_mul_five f g2 ga g0 ga g2, hg2m, hgam, hg0m]
      exact h3ReflMat_5 hα h2
  · refine ⟨g2 * ga * g1 * ga * g2, ?_, ?_⟩
    · exact h3Mats_mul_mem f (h3Mats_mul_mem f (h3Mats_mul_mem f
        (h3Mats_mul_mem f hg2 hga) hg1) hga) hg2
    · rw [toMatrix_mul_five f g2 ga g1 ga g2, hg2m, hgam, hg1m]
      exact h3ReflMat_6 hα h2
  · refine ⟨ga * g1 * ga, h3Mats_mul_mem f (h3Mats_mul_mem f hga hg1) hga, ?_⟩
    rw [toMatrix_mul_three f ga g1 ga, hgam, hg1m]
    exact h3ReflMat_7 hα h2

theorem exists_mem_h3Mats_refl {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) (j : Fin 8) :
    ∃ g ∈ basisClosure f (h3Mats α), LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec (h3ReflRoot α j) (h3ReflCoroot α j) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd (seven_lt_of_sq_eq_add_one (by norm_num) hα) (by norm_num)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  obtain ⟨g0, hg0, hg0m⟩ := exists_mem_basisClosure_toMatrix_eq f
    (diagSignMat_mem_h3Mats_four α 0) (isUnit_diagSignMat_det_four 0)
  obtain ⟨g1, hg1, hg1m⟩ := exists_mem_basisClosure_toMatrix_eq f
    (diagSignMat_mem_h3Mats_four α 1) (isUnit_diagSignMat_det_four 1)
  obtain ⟨g2, hg2, hg2m⟩ := exists_mem_basisClosure_toMatrix_eq f
    (diagSignMat_mem_h3Mats_four α 2) (isUnit_diagSignMat_det_four 2)
  obtain ⟨ga, hga, hgam⟩ := exists_mem_basisClosure_toMatrix_eq f
    (blockSucc_h3BlockMat_mem_h3Mats α) (isUnit_blockSucc_h3BlockMat_det hα h2)
  exact h3Mats_refl_case f hα h2 hg0 hg1 hg2 hga hg0m hg1m hg2m hgam j


private theorem h3ReflCoroot_dot_root {α : ZMod p} (hα : α ^ 2 = α + 1) (j : Fin 8) :
    ∑ i, h3ReflCoroot α j i * h3ReflRoot α j i = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd (seven_lt_of_sq_eq_add_one (by norm_num) hα) (by norm_num)
    exact ZMod.prime_ne_zero p 2 hp2
  fin_cases j <;>
    simp [h3ReflRoot, h3ReflCoroot, Fin.sum_univ_four] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [hα]) <;> (try ring)

private theorem h3_etaOK_first {α : ZMod p} (f : Module.Basis (Fin 4) (ZMod p) U) {w : U}
    {ψ : Module.Dual (ZMod p) U} (h2 : (2 : ZMod p) ≠ 0) (hψ0 : ψ (f 0) = 0)
    (hw0 : f.repr w 0 = 0)
    (hj : ∀ j : Fin 8, EtaOK 5 (∑ i, ψ (f i) * h3ReflRoot α j i)
      (∑ i, h3ReflCoroot α j i * f.repr w i)) :
    EtaOK 5 (ψ (f 1)) (2 * f.repr w 1) ∧
    EtaOK 5 (ψ (f 2)) (2 * f.repr w 2) ∧
    EtaOK 5 ((1 + α) * (ψ (f 1) + 1 * ψ (f 2)))
      ((f.repr w 1 + 1 * (2 - α) * f.repr w 2) / 2) ∧
    EtaOK 5 ((1 + α) * (ψ (f 1) + (-1) * ψ (f 2)))
      ((f.repr w 1 + (-1) * (2 - α) * f.repr w 2) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hj 0
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 0 i) = ψ (f 1) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0],
        show (∑ i, h3ReflCoroot α 0 i * f.repr w i) = 2 * f.repr w 1 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]] at h
  · have h := hj 1
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 1 i) = ψ (f 2) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0],
        show (∑ i, h3ReflCoroot α 1 i * f.repr w i) = 2 * f.repr w 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]] at h
  · have h := hj 2
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 2 i) =
            (1 + α) * (ψ (f 1) + 1 * ψ (f 2)) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0]; ring,
        show (∑ i, h3ReflCoroot α 2 i * f.repr w i) =
            (f.repr w 1 + 1 * (2 - α) * f.repr w 2) / 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]; field_simp] at h
  · have h := hj 3
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 3 i) =
            (1 + α) * (ψ (f 1) + (-1) * ψ (f 2)) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0]; ring,
        show (∑ i, h3ReflCoroot α 3 i * f.repr w i) =
            (f.repr w 1 + (-1) * (2 - α) * f.repr w 2) / 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]; field_simp] at h

private theorem h3_etaOK_second {α : ZMod p} (f : Module.Basis (Fin 4) (ZMod p) U) {w : U}
    {ψ : Module.Dual (ZMod p) U} (h2 : (2 : ZMod p) ≠ 0) (hψ0 : ψ (f 0) = 0)
    (hw0 : f.repr w 0 = 0)
    (hj : ∀ j : Fin 8, EtaOK 5 (∑ i, ψ (f i) * h3ReflRoot α j i)
      (∑ i, h3ReflCoroot α j i * f.repr w i)) :
    EtaOK 5 ((α - 1) * (ψ (f 1) + 1 * ψ (f 2)))
      ((α * f.repr w 1 + 1 * (α - 1) * f.repr w 2) / 2) ∧
    EtaOK 5 ((α - 1) * (ψ (f 1) + (-1) * ψ (f 2)))
      ((α * f.repr w 1 + (-1) * (α - 1) * f.repr w 2) / 2) ∧
    EtaOK 5 ((1 - α) * ψ (f 1) + 1 * (1 + α) * ψ (f 2))
      (((1 - α) * f.repr w 1 + 1 * f.repr w 2) / 2) ∧
    EtaOK 5 ((1 - α) * ψ (f 1) + (-1) * (1 + α) * ψ (f 2))
      (((1 - α) * f.repr w 1 + (-1) * f.repr w 2) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hj 4
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 4 i) =
            (α - 1) * (ψ (f 1) + 1 * ψ (f 2)) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0]; ring,
        show (∑ i, h3ReflCoroot α 4 i * f.repr w i) =
            (α * f.repr w 1 + 1 * (α - 1) * f.repr w 2) / 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]; field_simp] at h
  · have h := hj 5
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 5 i) =
            (α - 1) * (ψ (f 1) + (-1) * ψ (f 2)) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0]; ring,
        show (∑ i, h3ReflCoroot α 5 i * f.repr w i) =
            (α * f.repr w 1 + (-1) * (α - 1) * f.repr w 2) / 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]; field_simp] at h
  · have h := hj 6
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 6 i) =
            (1 - α) * ψ (f 1) + 1 * (1 + α) * ψ (f 2) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0]; ring,
        show (∑ i, h3ReflCoroot α 6 i * f.repr w i) =
            ((1 - α) * f.repr w 1 + 1 * f.repr w 2) / 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]; field_simp] at h
  · have h := hj 7
    rwa [show (∑ i, ψ (f i) * h3ReflRoot α 7 i) =
            (1 - α) * ψ (f 1) + (-1) * (1 + α) * ψ (f 2) by
          simp [h3ReflRoot, Fin.sum_univ_four, hψ0]; ring,
        show (∑ i, h3ReflCoroot α 7 i * f.repr w i) =
            ((1 - α) * f.repr w 1 + (-1) * f.repr w 2) / 2 by
          simp [h3ReflCoroot, Fin.sum_univ_four, hw0]; field_simp] at h

theorem h3EtaConstraints_of_toMatrix (hp5 : p ≠ 5) {α : ZMod p} (hα : α ^ 2 = α + 1)
    [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 5)
    (f : Module.Basis (Fin 4) (ZMod p) U) {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hb : Module.reflection hψ ∈ G) (hw0 : f.repr w 0 = 0) (hψ0 : ψ (f 0) = 0)
    (hr : ∀ j : Fin 8, ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        1 - Matrix.vecMulVec (h3ReflRoot α j) (h3ReflCoroot α j)) :
    H3EtaConstraints α (f.repr w 1) (f.repr w 2) (ψ (f 1)) (ψ (f 2)) := by
  have hdp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have hdp : 5 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hj : ∀ j : Fin 8, EtaOK 5 (∑ i, ψ (f i) * h3ReflRoot α j i)
      (∑ i, h3ReflCoroot α j i * f.repr w i) := by
    intro j
    obtain ⟨g, hgG, hgne, hgmat⟩ := hr j
    exact etaOK_of_toMatrix hG (by norm_num) hdp hp2 f hb hgG (Ne.symm hgne) hψ rfl hgmat
      (h3ReflCoroot_dot_root hα j)
  obtain ⟨e0, e1, e2, e3⟩ := h3_etaOK_first f h2 hψ0 hw0 hj
  obtain ⟨e4, e5, e6, e7⟩ := h3_etaOK_second f h2 hψ0 hw0 hj
  unfold H3EtaConstraints
  refine ⟨e0, e1, ?_⟩
  intro s hs
  rcases hs with h | h
  · subst h
    exact ⟨e2, e4, e6⟩
  · subst h
    exact ⟨e3, e5, e7⟩


private theorem exists_cand_case1 (hp5 : p ≠ 5) {α w₁ w₂ ψ₁ ψ₂ : ZMod p}
    (hα : α ^ 2 = α + 1) (h11 : 2 * (ψ₁ * w₁) = 2 - α) (h22 : 2 * (ψ₂ * w₂) = 1)
    (hC : h3Cross α w₁ w₂ ψ₁ ψ₂ = α / 2 - 1 ∨
      h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 - α / 2) :
    ∃ (k : Fin 3) (s : ZMod p), (s = 1 ∨ s = -1) ∧
      ψ₁ * w₁ = h4CandCoroot α k 1 * h4CandRoot α k 1 ∧
      s * (ψ₁ * w₂) = h4CandCoroot α k 1 * h4CandRoot α k 2 ∧
      s * (ψ₂ * w₁) = h4CandCoroot α k 2 * h4CandRoot α k 1 ∧
      ψ₂ * w₂ = h4CandCoroot α k 2 * h4CandRoot α k 2 := by
  have hp2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 (by
    have := seven_lt_of_sq_eq_add_one hp5 hα; omega)
  have hψ1 : ψ₁ * w₁ = (2 - α) / 2 := by rw [eq_div_iff hp2]; linear_combination h11
  have hψ2 : ψ₂ * w₂ = 1 / 2 := by rw [eq_div_iff hp2]; linear_combination h22
  rcases hC with hC | hC
  · have hrel : ψ₁ * w₁ * (ψ₂ * w₂) =
        (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2 := by
      rw [hψ1, hψ2, hC]
      all_goals (try field_simp)
      all_goals (try ring_nf)
      all_goals (try simp only [alphaP3 hα, alphaP2 hα])
      all_goals ring
    obtain ⟨hx, hy⟩ := h3Cross_eq hα hrel
    refine ⟨0, 1, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;>
      (try simp [h4CandRoot, h4CandCoroot]) <;>
      (try rw [hψ1]) <;> (try rw [hψ2]) <;> (try rw [hx]) <;> (try rw [hy]) <;>
      (try rw [hC]) <;> (try field_simp) <;> (try ring_nf) ;
      (try simp only [alphaP2 hα]) ; ring
  · have hrel : ψ₁ * w₁ * (ψ₂ * w₂) =
        (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2 := by
      rw [hψ1, hψ2, hC]
      all_goals (try field_simp)
      all_goals (try ring_nf)
      all_goals (try simp only [alphaP3 hα, alphaP2 hα])
      all_goals ring
    obtain ⟨hx, hy⟩ := h3Cross_eq hα hrel
    refine ⟨0, -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;>
      (try simp [h4CandRoot, h4CandCoroot]) <;>
      (try rw [hψ1]) <;> (try rw [hψ2]) <;> (try rw [hx]) <;> (try rw [hy]) <;>
      (try rw [hC]) <;> (try field_simp) <;> (try ring_nf) ;
      (try simp only [alphaP2 hα]) ; ring

private theorem exists_cand_case2 (hp5 : p ≠ 5) {α w₁ w₂ ψ₁ ψ₂ : ZMod p}
    (hα : α ^ 2 = α + 1) (h11 : 2 * (ψ₁ * w₁) = 1 + α) (h22 : 2 * (ψ₂ * w₂) = 2 - α)
    (hC : h3Cross α w₁ w₂ ψ₁ ψ₂ = (1 - α) / 2 ∨
      h3Cross α w₁ w₂ ψ₁ ψ₂ = (α - 1) / 2) :
    ∃ (k : Fin 3) (s : ZMod p), (s = 1 ∨ s = -1) ∧
      ψ₁ * w₁ = h4CandCoroot α k 1 * h4CandRoot α k 1 ∧
      s * (ψ₁ * w₂) = h4CandCoroot α k 1 * h4CandRoot α k 2 ∧
      s * (ψ₂ * w₁) = h4CandCoroot α k 2 * h4CandRoot α k 1 ∧
      ψ₂ * w₂ = h4CandCoroot α k 2 * h4CandRoot α k 2 := by
  have hp2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 (by
    have := seven_lt_of_sq_eq_add_one hp5 hα; omega)
  have hψ1 : ψ₁ * w₁ = (1 + α) / 2 := by rw [eq_div_iff hp2]; linear_combination h11
  have hψ2 : ψ₂ * w₂ = (2 - α) / 2 := by rw [eq_div_iff hp2]; linear_combination h22
  rcases hC with hC | hC
  · have hrel : ψ₁ * w₁ * (ψ₂ * w₂) =
        (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2 := by
      rw [hψ1, hψ2, hC]
      all_goals (try field_simp)
      all_goals (try ring_nf)
      all_goals (try simp only [alphaP3 hα, alphaP2 hα])
      all_goals ring
    obtain ⟨hx, hy⟩ := h3Cross_eq hα hrel
    refine ⟨1, 1, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;>
      (try simp [h4CandRoot, h4CandCoroot]) <;>
      (try rw [hψ1]) <;> (try rw [hψ2]) <;> (try rw [hx]) <;> (try rw [hy]) <;>
      (try rw [hC]) <;> (try field_simp) ; (try ring_nf) ;
      (try simp only [alphaP2 hα]) ; ring
  · have hrel : ψ₁ * w₁ * (ψ₂ * w₂) =
        (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2 := by
      rw [hψ1, hψ2, hC]
      all_goals (try field_simp)
      all_goals (try ring_nf)
      all_goals (try simp only [alphaP3 hα, alphaP2 hα])
      all_goals ring
    obtain ⟨hx, hy⟩ := h3Cross_eq hα hrel
    refine ⟨1, -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;>
      (try simp [h4CandRoot, h4CandCoroot]) <;>
      (try rw [hψ1]) <;> (try rw [hψ2]) <;> (try rw [hx]) <;> (try rw [hy]) <;>
      (try rw [hC]) <;> (try field_simp) <;> (try ring_nf) ;
      (try simp only [alphaP2 hα]) ; ring

private theorem exists_cand_case3 (hp5 : p ≠ 5) {α w₁ w₂ ψ₁ ψ₂ : ZMod p}
    (hα : α ^ 2 = α + 1) (h11 : 2 * (ψ₁ * w₁) = 1) (h22 : 2 * (ψ₂ * w₂) = 1 + α)
    (hC : h3Cross α w₁ w₂ ψ₁ ψ₂ = 1 / 2 ∨
      h3Cross α w₁ w₂ ψ₁ ψ₂ = -(1 / 2)) :
    ∃ (k : Fin 3) (s : ZMod p), (s = 1 ∨ s = -1) ∧
      ψ₁ * w₁ = h4CandCoroot α k 1 * h4CandRoot α k 1 ∧
      s * (ψ₁ * w₂) = h4CandCoroot α k 1 * h4CandRoot α k 2 ∧
      s * (ψ₂ * w₁) = h4CandCoroot α k 2 * h4CandRoot α k 1 ∧
      ψ₂ * w₂ = h4CandCoroot α k 2 * h4CandRoot α k 2 := by
  have hp2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 (by
    have := seven_lt_of_sq_eq_add_one hp5 hα; omega)
  have hψ1 : ψ₁ * w₁ = 1 / 2 := by rw [eq_div_iff hp2]; linear_combination h11
  have hψ2 : ψ₂ * w₂ = (1 + α) / 2 := by rw [eq_div_iff hp2]; linear_combination h22
  rcases hC with hC | hC
  · have hrel : ψ₁ * w₁ * (ψ₂ * w₂) =
        (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2 := by
      rw [hψ1, hψ2, hC]
      all_goals (try field_simp)
    obtain ⟨hx, hy⟩ := h3Cross_eq hα hrel
    refine ⟨2, -1, Or.inr rfl, ?_, ?_, ?_, ?_⟩ <;>
      (try simp [h4CandRoot, h4CandCoroot]) <;>
      (try rw [hψ1]) <;> (try rw [hψ2]) <;> (try rw [hx]) <;> (try rw [hy]) <;>
      (try rw [hC]) <;> (try field_simp) <;> (try ring_nf)
  · have hrel : ψ₁ * w₁ * (ψ₂ * w₂) =
        (1 + α) * h3Cross α w₁ w₂ ψ₁ ψ₂ ^ 2 := by
      rw [hψ1, hψ2, hC]
      all_goals (try field_simp)
    obtain ⟨hx, hy⟩ := h3Cross_eq hα hrel
    refine ⟨2, 1, Or.inl rfl, ?_, ?_, ?_, ?_⟩ <;>
      (try simp [h4CandRoot, h4CandCoroot]) <;>
      (try rw [hψ1]) <;> (try rw [hψ2]) <;> (try rw [hx]) <;> (try rw [hy]) <;>
      (try rw [hC]) <;> (try field_simp) <;> (try ring_nf)

theorem H3EtaConstraints.exists_cand (hp5 : p ≠ 5) {α w₁ w₂ ψ₁ ψ₂ : ZMod p}
    (hα : α ^ 2 = α + 1) (hc : H3EtaConstraints α w₁ w₂ ψ₁ ψ₂) (hw : w₁ ≠ 0 ∨ w₂ ≠ 0)
    (h2 : ψ₁ * w₁ + ψ₂ * w₂ ≠ 2) :
    ∃ (k : Fin 3) (s : ZMod p), (s = 1 ∨ s = -1) ∧
      ψ₁ * w₁ = h4CandCoroot α k 1 * h4CandRoot α k 1 ∧
      s * (ψ₁ * w₂) = h4CandCoroot α k 1 * h4CandRoot α k 2 ∧
      s * (ψ₂ * w₁) = h4CandCoroot α k 2 * h4CandRoot α k 1 ∧
      ψ₂ * w₂ = h4CandCoroot α k 2 * h4CandRoot α k 2 := by
  rcases H3EtaConstraints.classify hp5 hα hc hw h2 with
    ⟨h11, h22, hC⟩ | ⟨h11, h22, hC⟩ | ⟨h11, h22, hC⟩
  · exact exists_cand_case1 hp5 hα h11 h22 hC
  · exact exists_cand_case2 hp5 hα h11 h22 hC
  · exact exists_cand_case3 hp5 hα h11 h22 hC

private theorem h4CandRoot_zero (α : ZMod p) (k : Fin 3) : h4CandRoot α k 0 = 0 := by
  fin_cases k <;> simp [h4CandRoot]

private theorem h4CandCoroot_zero (α : ZMod p) (k : Fin 3) : h4CandCoroot α k 0 = 0 := by
  fin_cases k <;> simp [h4CandCoroot]

private theorem h4CandRoot_one (α : ZMod p) (k : Fin 3) : h4CandRoot α k 1 = 1 := by
  fin_cases k <;> simp [h4CandRoot]

private theorem alpha_ne_zero {α : ZMod p} (hα : α ^ 2 = α + 1) : α ≠ 0 := by
  intro h; rw [h] at hα
  exact one_ne_zero (by linear_combination -hα)

private theorem alpha_ne_one {α : ZMod p} (hα : α ^ 2 = α + 1) : α ≠ 1 := by
  intro h; rw [h] at hα
  exact one_ne_zero (by linear_combination -hα)

private theorem alpha_ne_neg_one {α : ZMod p} (hα : α ^ 2 = α + 1) : α ≠ -1 := by
  intro h; rw [h] at hα
  exact one_ne_zero (by linear_combination hα)

private theorem alpha_ne_two {α : ZMod p} (hα : α ^ 2 = α + 1) : α ≠ 2 := by
  intro h; rw [h] at hα
  exact one_ne_zero (by linear_combination hα)

private theorem two_ne_zero_of_sq_eq_add_one {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (2 : ZMod p) ≠ 0 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (by decide +revert : ∀ x : ZMod 2, x ^ 2 ≠ x + 1) α hα
  exact ZMod.prime_ne_zero p 2 hp2

private theorem h4CandCoroot_one_ne_zero {α : ZMod p} (hα : α ^ 2 = α + 1) (k : Fin 3) :
    h4CandCoroot α k 1 ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_sq_eq_add_one hα
  have ha2 : α ≠ 2 := alpha_ne_two hα
  have han1 : (1 + α : ZMod p) ≠ 0 := by
    intro h; exact alpha_ne_neg_one hα (by linear_combination h)
  fin_cases k
  · simp only [h4CandCoroot]
    rw [show (1 : ZMod p) - α / 2 = (2 - α) / 2 by field_simp]
    exact div_ne_zero (by intro h; rw [sub_eq_zero] at h; exact ha2 h.symm) h2
  · simp only [h4CandCoroot]
    exact div_ne_zero han1 h2
  · simp only [h4CandCoroot]
    exact div_ne_zero one_ne_zero h2

private theorem h4CandRoot_three_ne_zero {α : ZMod p} (hα : α ^ 2 = α + 1) (k : Fin 3) :
    h4CandRoot α k 3 ≠ 0 := by
  have ha1' : (α - 1 : ZMod p) ≠ 0 := by
    intro h; exact alpha_ne_one hα (by linear_combination h)
  have han1' : (1 + α : ZMod p) ≠ 0 := by
    intro h; exact alpha_ne_neg_one hα (by linear_combination h)
  fin_cases k <;> simp only [h4CandRoot] <;> assumption

private theorem h4CandRoot_three_mul_coroot_three_ne_zero {α : ZMod p} (hα : α ^ 2 = α + 1)
    (k : Fin 3) : h4CandRoot α k 3 * h4CandCoroot α k 3 ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_sq_eq_add_one hα
  have ha0 : α ≠ 0 := alpha_ne_zero hα
  have ha1' : (α - 1 : ZMod p) ≠ 0 := by
    intro h; exact alpha_ne_one hα (by linear_combination h)
  have han1' : (1 + α : ZMod p) ≠ 0 := by
    intro h; exact alpha_ne_neg_one hα (by linear_combination h)
  fin_cases k
  · simp only [h4CandRoot, h4CandCoroot]
    exact mul_ne_zero han1' (div_ne_zero one_ne_zero h2)
  · simp only [h4CandRoot, h4CandCoroot]
    exact mul_ne_zero ha1' (div_ne_zero ha0 h2)
  · simp only [h4CandRoot, h4CandCoroot]
    exact mul_ne_zero ha1' (div_ne_zero ha1' h2)

private theorem h4Cand_dot_root {α : ZMod p} (hα : α ^ 2 = α + 1) (k : Fin 3) :
    ∑ i, h4CandCoroot α k i * h4CandRoot α k i = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_sq_eq_add_one hα
  fin_cases k <;>
    simp [h4CandRoot, h4CandCoroot, Fin.sum_univ_four] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [hα]) <;> (try ring)

private theorem h4Cand_kappa3_rho3 {α : ZMod p} (hα : α ^ 2 = α + 1) {ρ κ : Fin 4 → ZMod p}
    (hρ0 : ρ 0 = 0) (hκ0 : κ 0 = 0) (hκρ : ∑ i, κ i * ρ i = 2) (k : Fin 3)
    (h11 : κ 1 * ρ 1 = h4CandCoroot α k 1 * h4CandRoot α k 1)
    (h22 : κ 2 * ρ 2 = h4CandCoroot α k 2 * h4CandRoot α k 2) :
    κ 3 * ρ 3 = h4CandRoot α k 3 * h4CandCoroot α k 3 := by
  have hκρ' : κ 1 * ρ 1 + κ 2 * ρ 2 + κ 3 * ρ 3 = 2 := by
    have h := hκρ
    rw [Fin.sum_univ_four, hκ0, hρ0, zero_mul, zero_add] at h
    simpa [add_assoc] using h
  have hcand' : h4CandCoroot α k 1 * h4CandRoot α k 1 +
      h4CandCoroot α k 2 * h4CandRoot α k 2 +
      h4CandCoroot α k 3 * h4CandRoot α k 3 = 2 := by
    have h := h4Cand_dot_root hα k
    rw [Fin.sum_univ_four, h4CandCoroot_zero α k, zero_mul, zero_add] at h
    simpa [add_assoc] using h
  rw [← h11, ← h22] at hcand'
  linear_combination hκρ' - hcand'

private theorem h4Cand_kappa_one_ne_zero {α : ZMod p} {ρ κ : Fin 4 → ZMod p} (k : Fin 3)
    (h11 : κ 1 * ρ 1 = h4CandCoroot α k 1 * h4CandRoot α k 1)
    (hc1 : h4CandCoroot α k 1 ≠ 0) : κ 1 ≠ 0 := by
  have hr1 : h4CandRoot α k 1 = 1 := h4CandRoot_one α k
  intro hk
  apply hc1
  have hh := h11
  rw [hk, zero_mul, hr1, mul_one] at hh
  exact hh.symm

private theorem h4Cand_rho_three_ne_zero {α : ZMod p} {ρ κ : Fin 4 → ZMod p} (k : Fin 3)
    (hκ3ρ3 : κ 3 * ρ 3 = h4CandRoot α k 3 * h4CandCoroot α k 3)
    (hr3c3 : h4CandRoot α k 3 * h4CandCoroot α k 3 ≠ 0) : ρ 3 ≠ 0 := by
  intro h
  apply hr3c3
  rw [← hκ3ρ3, h, mul_zero]

private theorem diagonal_conj_one_sub_vecMulVec {n : ℕ} (a : Fin n → (ZMod p)ˣ)
    (ρ κ : Fin n → ZMod p) :
    Matrix.diagonal (fun i => ((a i : ZMod p))⁻¹) * (1 - Matrix.vecMulVec ρ κ) *
      Matrix.diagonal (fun i => (a i : ZMod p)) =
    1 - Matrix.vecMulVec (fun i => ((a i : ZMod p))⁻¹ * ρ i)
      (fun j => κ j * (a j : ZMod p)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  have hne : (a i : ZMod p) ≠ 0 := (a i).ne_zero
  by_cases h : i = j
  · subst h
    field_simp
  · rw [if_neg h]; ring

private theorem h4Cand_conj_rho {α : ZMod p} (k : Fin 3) (w : Fin 4 → (ZMod p)ˣ)
    {ρ κ : Fin 4 → ZMod p} (hρ0 : ρ 0 = 0) (hκ1 : κ 1 ≠ 0) (hρ3 : ρ 3 ≠ 0)
    (h11 : κ 1 * ρ 1 = h4CandCoroot α k 1 * h4CandRoot α k 1)
    (h12 : κ 1 * ρ 2 = h4CandCoroot α k 1 * h4CandRoot α k 2)
    (hw0 : w 0 = 1) (hw1 : w 1 = 1) (hw2 : w 2 = 1)
    (hw3 : (w 3 : ZMod p) = ρ 3 * κ 1 / (h4CandRoot α k 3 * h4CandCoroot α k 1)) :
    (fun i => ((w i : ZMod p))⁻¹ * ρ i) =
        fun i => (h4CandCoroot α k 1 / κ 1) * h4CandRoot α k i := by
  have hr1 : h4CandRoot α k 1 = 1 := h4CandRoot_one α k
  have h11' : κ 1 * ρ 1 = h4CandCoroot α k 1 := by rw [h11, hr1, mul_one]
  funext i
  fin_cases i
  · change ((w 0 : ZMod p))⁻¹ * ρ 0 = (h4CandCoroot α k 1 / κ 1) * h4CandRoot α k 0
    simp [hw0, hρ0, h4CandRoot_zero α k]
  · change ((w 1 : ZMod p))⁻¹ * ρ 1 = (h4CandCoroot α k 1 / κ 1) * h4CandRoot α k 1
    rw [hw1, Units.val_one, inv_one, one_mul, hr1, mul_one]
    field_simp
    linear_combination h11'
  · change ((w 2 : ZMod p))⁻¹ * ρ 2 = (h4CandCoroot α k 1 / κ 1) * h4CandRoot α k 2
    rw [hw2, Units.val_one, inv_one, one_mul]
    field_simp
    linear_combination h12
  · change ((w 3 : ZMod p))⁻¹ * ρ 3 = (h4CandCoroot α k 1 / κ 1) * h4CandRoot α k 3
    rw [hw3]
    field_simp [hρ3]

private theorem h4Cand_conj_kappa {α : ZMod p} (k : Fin 3) (w : Fin 4 → (ZMod p)ˣ)
    {ρ κ : Fin 4 → ZMod p} (hκ0 : κ 0 = 0) (hc1 : h4CandCoroot α k 1 ≠ 0)
    (hr3 : h4CandRoot α k 3 ≠ 0)
    (h11 : κ 1 * ρ 1 = h4CandCoroot α k 1 * h4CandRoot α k 1)
    (h21 : κ 2 * ρ 1 = h4CandCoroot α k 2 * h4CandRoot α k 1)
    (hκ3ρ3 : κ 3 * ρ 3 = h4CandRoot α k 3 * h4CandCoroot α k 3)
    (hw0 : w 0 = 1) (hw1 : w 1 = 1) (hw2 : w 2 = 1)
    (hw3 : (w 3 : ZMod p) = ρ 3 * κ 1 / (h4CandRoot α k 3 * h4CandCoroot α k 1)) :
    (fun j => κ j * (w j : ZMod p)) =
        fun j => (κ 1 / h4CandCoroot α k 1) * h4CandCoroot α k j := by
  have hr1 : h4CandRoot α k 1 = 1 := h4CandRoot_one α k
  have h11' : κ 1 * ρ 1 = h4CandCoroot α k 1 := by rw [h11, hr1, mul_one]
  have h21' : κ 2 * ρ 1 = h4CandCoroot α k 2 := by rw [h21, hr1, mul_one]
  have hc1c2 : h4CandCoroot α k 1 * κ 2 = h4CandCoroot α k 2 * κ 1 := by
    calc h4CandCoroot α k 1 * κ 2 = (κ 1 * ρ 1) * κ 2 := by rw [h11']
      _ = κ 1 * (κ 2 * ρ 1) := by ring
      _ = κ 1 * h4CandCoroot α k 2 := by rw [h21']
      _ = h4CandCoroot α k 2 * κ 1 := by ring
  funext j
  fin_cases j
  · change κ 0 * (w 0 : ZMod p) = (κ 1 / h4CandCoroot α k 1) * h4CandCoroot α k 0
    simp [hw0, hκ0, h4CandCoroot_zero α k]
  · change κ 1 * (w 1 : ZMod p) = (κ 1 / h4CandCoroot α k 1) * h4CandCoroot α k 1
    rw [hw1, Units.val_one, mul_one]
    field_simp [hc1]
  · change κ 2 * (w 2 : ZMod p) = (κ 1 / h4CandCoroot α k 1) * h4CandCoroot α k 2
    rw [hw2, Units.val_one, mul_one]
    field_simp [hc1]
    linear_combination hc1c2
  · change κ 3 * (w 3 : ZMod p) = (κ 1 / h4CandCoroot α k 1) * h4CandCoroot α k 3
    rw [hw3]
    field_simp [hr3, hc1]
    rw [hκ3ρ3]
    ring

private theorem toMatrix_unitsSMul_update_eq_h4CandMat {α : ZMod p}
    (f : Module.Basis (Fin 4) (ZMod p) U) (w : Fin 4 → (ZMod p)ˣ) (k : Fin 3)
    {c : U ≃ₗ[ZMod p] U} {ρ κ : Fin 4 → ZMod p} (hκ1 : κ 1 ≠ 0)
    (hc1 : h4CandCoroot α k 1 ≠ 0)
    (hc : LinearMap.toMatrix f f (c : U →ₗ[ZMod p] U) = 1 - Matrix.vecMulVec ρ κ)
    (hρ' : (fun i : Fin 4 => ((w i : ZMod p))⁻¹ * ρ i) =
        fun i : Fin 4 => (h4CandCoroot α k 1 / κ 1) * h4CandRoot α k i)
    (hκ' : (fun j : Fin 4 => κ j * (w j : ZMod p)) =
        fun j : Fin 4 => (κ 1 / h4CandCoroot α k 1) * h4CandCoroot α k j) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) (c : U →ₗ[ZMod p] U) =
        h4CandMat α k := by
  have hD : f.toMatrix (f.unitsSMul w) = Matrix.diagonal (fun i => (w i : ZMod p)) :=
    f.toMatrix_unitsSMul _
  have hDinv : (Matrix.diagonal (fun i => (w i : ZMod p)))⁻¹ =
      Matrix.diagonal (fun i => ((w i : ZMod p))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    ext i j
    rw [Matrix.diagonal_mul_diagonal]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact mul_inv_cancel₀ (Units.ne_zero (w i))
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  rw [toMatrix_unitsSMul_conj f w c, hc, hD, hDinv,
    diagonal_conj_one_sub_vecMulVec w ρ κ, hρ', hκ', h4CandMat]
  ext i j
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  field_simp [hκ1, hc1]

theorem exists_toMatrix_unitsSMul_eq_h4CandMat {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) {c : U ≃ₗ[ZMod p] U} {ρ κ : Fin 4 → ZMod p}
    (hc : LinearMap.toMatrix f f (c : U →ₗ[ZMod p] U) = 1 - Matrix.vecMulVec ρ κ)
    (hρ0 : ρ 0 = 0) (hκ0 : κ 0 = 0) (hκρ : ∑ i, κ i * ρ i = 2) (k : Fin 3)
    (h11 : κ 1 * ρ 1 = h4CandCoroot α k 1 * h4CandRoot α k 1)
    (h12 : κ 1 * ρ 2 = h4CandCoroot α k 1 * h4CandRoot α k 2)
    (h21 : κ 2 * ρ 1 = h4CandCoroot α k 2 * h4CandRoot α k 1)
    (h22 : κ 2 * ρ 2 = h4CandCoroot α k 2 * h4CandRoot α k 2) :
    ∃ μ : (ZMod p)ˣ, LinearMap.toMatrix (f.unitsSMul (Function.update 1 (Fin.last 3) μ))
      (f.unitsSMul (Function.update 1 (Fin.last 3) μ)) (c : U →ₗ[ZMod p] U) = h4CandMat α k := by
  have hc1 : h4CandCoroot α k 1 ≠ 0 := h4CandCoroot_one_ne_zero hα k
  have hr3 : h4CandRoot α k 3 ≠ 0 := h4CandRoot_three_ne_zero hα k
  have hr3c3 : h4CandRoot α k 3 * h4CandCoroot α k 3 ≠ 0 :=
    h4CandRoot_three_mul_coroot_three_ne_zero hα k
  have hκ3ρ3 : κ 3 * ρ 3 = h4CandRoot α k 3 * h4CandCoroot α k 3 :=
    h4Cand_kappa3_rho3 hα hρ0 hκ0 hκρ k h11 h22
  have hκ1 : κ 1 ≠ 0 := h4Cand_kappa_one_ne_zero k h11 hc1
  have hρ3 : ρ 3 ≠ 0 := h4Cand_rho_three_ne_zero k hκ3ρ3 hr3c3
  have hμnz : ρ 3 * κ 1 / (h4CandRoot α k 3 * h4CandCoroot α k 1) ≠ 0 :=
    div_ne_zero (mul_ne_zero hρ3 hκ1) (mul_ne_zero hr3 hc1)
  let μ : (ZMod p)ˣ := Units.mk0 _ hμnz
  let w : Fin 4 → (ZMod p)ˣ := Function.update 1 (Fin.last 3) μ
  have hw0 : w 0 = 1 := by simp [w]
  have hw1 : w 1 = 1 := by simp [w]
  have hw2 : w 2 = 1 := by simp [w]
  have hw3u : w 3 = μ := by simp [w]
  have hμval : ((μ : ZMod p)) = ρ 3 * κ 1 / (h4CandRoot α k 3 * h4CandCoroot α k 1) := rfl
  have hw3 : (w 3 : ZMod p) =
      ρ 3 * κ 1 / (h4CandRoot α k 3 * h4CandCoroot α k 1) := by rw [hw3u, hμval]
  refine ⟨μ, ?_⟩
  exact toMatrix_unitsSMul_update_eq_h4CandMat f w k hκ1 hc1 hc
    (h4Cand_conj_rho k w hρ0 hκ1 hρ3 h11 h12 hw0 hw1 hw2 hw3)
    (h4Cand_conj_kappa k w hκ0 hc1 hr3 h11 h21 hκ3ρ3 hw0 hw1 hw2 hw3)

private theorem isUnit_det_diagSignMat_four (i : Fin 4) :
    IsUnit (diagSignMat i : Matrix (Fin 4) (Fin 4) (ZMod p)).det := by
  rw [show (diagSignMat i : Matrix (Fin 4) (Fin 4) (ZMod p)).det = -1 by
    simp [diagSignMat, Matrix.det_diagonal]]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

private theorem exists_mem_of_diagSignMat {α : ZMod p} (f' : Module.Basis (Fin 4) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hH' : basisClosure f' (h3Mats α) ≤ G) (i : Fin 3) :
    ∃ d ∈ G, LinearMap.toMatrix f' f' (d : U →ₗ[ZMod p] U) = diagSignMat (Fin.castSucc i) := by
  have hdet : IsUnit (diagSignMat (Fin.castSucc i) : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    isUnit_det_diagSignMat_four _
  have hmem : (diagSignMat (Fin.castSucc i) : Matrix (Fin 4) (Fin 4) (ZMod p)) ∈ h3Mats α := by
    refine ⟨diagSignMat i, ?_, ?_⟩
    · fin_cases i <;> simp [h3BlockMats]
    · rw [blockSucc_diagSignMat]
  obtain ⟨d, hd, hdm⟩ := exists_mem_basisClosure_toMatrix_eq f' hmem hdet
  exact ⟨d, hH' hd, hdm⟩

private theorem toMatrix_injective_of_basis (f' : Module.Basis (Fin 4) (ZMod p) U) :
    ∀ {g c : U ≃ₗ[ZMod p] U}, LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) → g = c := by
  intro g c h
  apply LinearEquiv.coe_injective
  funext x
  have := congrArg (fun M : Matrix (Fin 4) (Fin 4) (ZMod p) => Matrix.mulVec M (f'.repr x)) h
  rw [LinearMap.toMatrix_mulVec_repr, LinearMap.toMatrix_mulVec_repr] at this
  exact f'.repr.injective (by simpa using this)

private theorem mem_of_h4BlockMat_zero {α : ZMod p} (hα : α ^ 2 = α + 1)
    (h2 : (2 : ZMod p) ≠ 0) (f' : Module.Basis (Fin 4) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} {c g : U ≃ₗ[ZMod p] U} (hc : c ∈ G)
    (hmat_inj : ∀ {g c : U ≃ₗ[ZMod p] U},
      LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) =
        LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) → g = c)
    (hck : LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) = h4CandMat α 0)
    (hg : LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) = h4BlockMat α) : g ∈ G := by
  obtain ⟨h0, _, _⟩ := h4BlockMat_eq_h4CandMat h2 hα
  rw [h0] at hg
  rw [hmat_inj (hg.trans hck.symm)]
  exact hc

private theorem mem_of_h4BlockMat_one {α : ZMod p} (hα : α ^ 2 = α + 1)
    (h2 : (2 : ZMod p) ≠ 0) (f' : Module.Basis (Fin 4) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} {c d1 g : U ≃ₗ[ZMod p] U} (hc : c ∈ G) (hd1 : d1 ∈ G)
    (hmat_inj : ∀ {g c : U ≃ₗ[ZMod p] U},
      LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) =
        LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) → g = c)
    (hck : LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) = h4CandMat α 1)
    (hd1m : LinearMap.toMatrix f' f' (d1 : U →ₗ[ZMod p] U) = diagSignMat 1)
    (hg : LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) = h4BlockMat α) : g ∈ G := by
  obtain ⟨_, h1, _⟩ := h4BlockMat_eq_h4CandMat h2 hα
  rw [h1] at hg
  have hgg : g = c * d1 * c := hmat_inj (by
    rw [hg]
    rw [show (↑(c * d1 * c) : U →ₗ[ZMod p] U) =
      (c : U →ₗ[ZMod p] U) * (d1 : U →ₗ[ZMod p] U) * (c : U →ₗ[ZMod p] U) from rfl]
    simp only [LinearMap.toMatrix_mul, hck, hd1m])
  rw [hgg]; exact G.mul_mem (G.mul_mem hc hd1) hc

private theorem mem_of_h4BlockMat_two {α : ZMod p} (hα : α ^ 2 = α + 1)
    (h2 : (2 : ZMod p) ≠ 0) (f' : Module.Basis (Fin 4) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} {c d1 d2 g : U ≃ₗ[ZMod p] U}
    (hc : c ∈ G) (hd1 : d1 ∈ G) (hd2 : d2 ∈ G)
    (hmat_inj : ∀ {g c : U ≃ₗ[ZMod p] U},
      LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) =
        LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) → g = c)
    (hck : LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) = h4CandMat α 2)
    (hd1m : LinearMap.toMatrix f' f' (d1 : U →ₗ[ZMod p] U) = diagSignMat 1)
    (hd2m : LinearMap.toMatrix f' f' (d2 : U →ₗ[ZMod p] U) = diagSignMat 2)
    (hg : LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) = h4BlockMat α) : g ∈ G := by
  obtain ⟨_, _, h2w⟩ := h4BlockMat_eq_h4CandMat h2 hα
  rw [h2w] at hg
  have hgg : g = c * (d1 * d2) * c * (d1 * d2) * c := hmat_inj (by
    rw [hg]
    rw [show (↑(c * (d1 * d2) * c * (d1 * d2) * c) : U →ₗ[ZMod p] U) =
      (c : U →ₗ[ZMod p] U) * ((d1 : U →ₗ[ZMod p] U) * (d2 : U →ₗ[ZMod p] U)) *
        (c : U →ₗ[ZMod p] U) * ((d1 : U →ₗ[ZMod p] U) * (d2 : U →ₗ[ZMod p] U)) *
        (c : U →ₗ[ZMod p] U) from rfl]
    simp only [LinearMap.toMatrix_mul, hck, hd1m, hd2m])
  rw [hgg]
  exact G.mul_mem (G.mul_mem (G.mul_mem (G.mul_mem hc (G.mul_mem hd1 hd2)) hc)
    (G.mul_mem hd1 hd2)) hc

theorem basisClosure_h4BlockMats_le {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH : basisClosure f (h3Mats α) ≤ G) (μ : (ZMod p)ˣ) (k : Fin 3) {c : U ≃ₗ[ZMod p] U}
    (hc : c ∈ G)
    (hck : LinearMap.toMatrix (f.unitsSMul (Function.update 1 (Fin.last 3) μ))
      (f.unitsSMul (Function.update 1 (Fin.last 3) μ)) (c : U →ₗ[ZMod p] U) = h4CandMat α k) :
    basisClosure (f.unitsSMul (Function.update 1 (Fin.last 3) μ)) (h4BlockMats α) ≤ G := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd (seven_lt_of_sq_eq_add_one (by norm_num) hα) (by norm_num)
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  set w : Fin 4 → (ZMod p)ˣ := Function.update 1 (Fin.last 3) μ with hw
  set f' := f.unitsSMul w with hf'
  have hH' : basisClosure f' (h3Mats α) ≤ G := by
    rw [hf', hw, h3Mats, basisClosure_unitsSMul_blockSucc]
    exact hH
  obtain ⟨d1, hd1G, hd1m⟩ := exists_mem_of_diagSignMat f' hH' 1
  obtain ⟨d2, hd2G, hd2m⟩ := exists_mem_of_diagSignMat f' hH' 2
  have hmat_inj : ∀ {g c : U ≃ₗ[ZMod p] U},
      LinearMap.toMatrix f' f' (g : U →ₗ[ZMod p] U) =
        LinearMap.toMatrix f' f' (c : U →ₗ[ZMod p] U) → g = c :=
    toMatrix_injective_of_basis f'
  rw [basisClosure]
  apply (Subgroup.closure_le G).mpr
  intro g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  rw [h4BlockMats] at hg
  simp only [Set.mem_insert_iff] at hg
  rcases hg with hg | ⟨M, hM, hMg⟩
  · fin_cases k
    · exact mem_of_h4BlockMat_zero hα h2 f' hc hmat_inj hck hg
    · exact mem_of_h4BlockMat_one hα h2 f' hc hd1G hmat_inj hck hd1m hg
    · exact mem_of_h4BlockMat_two hα h2 f' hc hd1G hd2G hmat_inj hck hd1m hd2m hg
  · exact hH' (Subgroup.subset_closure ⟨M, hM, hMg⟩)
private theorem h3ReflMat_apply_last (α : ZMod p) (j : Fin 8) :
    (1 - Matrix.vecMulVec (h3ReflRoot α j) (h3ReflCoroot α j)) (3 : Fin 4) 3 = 1 := by
  fin_cases j <;>
    simp [h3ReflRoot, h3ReflCoroot, Matrix.sub_apply]

private theorem diagSignMat_one_conj_vecMulVec (ρ κ : Fin 4 → ZMod p) :
    diagSignMat (1 : Fin 4) * (1 - Matrix.vecMulVec ρ κ) * diagSignMat (1 : Fin 4) =
      1 - Matrix.vecMulVec (fun i => if i = 1 then -ρ i else ρ i)
        (fun j => if j = 1 then -κ j else κ j) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSignMat, Matrix.vecMulVec, Matrix.one_apply, Matrix.mul_apply,
      Matrix.sub_apply, Fin.sum_univ_four]

private theorem h3Refl_mem_ne_reflection {α : ZMod p} (f : Module.Basis (Fin 4) (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hH : basisClosure f (h3Mats α) ≤ G) (hα : α ^ 2 = α + 1)
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hbmat : LinearMap.toMatrix f f (Module.reflection hψ : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec (fun i => f.repr w i) (fun i => ψ (f i)))
    (hw3 : f.repr w 3 ≠ 0) (hψ3 : ψ (f 3) ≠ 0) :
    ∀ j : Fin 8, ∃ g ∈ G, g ≠ Module.reflection hψ ∧
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
        1 - Matrix.vecMulVec (h3ReflRoot α j) (h3ReflCoroot α j) := by
  intro j
  obtain ⟨g, hgH, hgmat⟩ := exists_mem_h3Mats_refl hα f j
  refine ⟨g, hH hgH, ?_, hgmat⟩
  intro hgb
  have hmat := hbmat
  rw [← hgb, hgmat] at hmat
  have h33 := congrFun (congrFun hmat (3 : Fin 4)) (3 : Fin 4)
  rw [h3ReflMat_apply_last α j] at h33
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply] at h33
  simp only [if_true] at h33
  exact (mul_ne_zero hw3 hψ3) (by linear_combination h33)

private theorem h4_psi_sum (f : Module.Basis (Fin 4) (ZMod p) U) {w : U}
    {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hw0 : f.repr w 0 = 0)
    (hψ0 : ψ (f 0) = 0) (hw3 : f.repr w 3 ≠ 0) (hψ3 : ψ (f 3) ≠ 0) :
    (∑ i, ψ (f i) * f.repr w i = 2) ∧
      ψ (f 1) * f.repr w 1 + ψ (f 2) * f.repr w 2 ≠ 2 := by
  have hψw : ∑ i, ψ (f i) * f.repr w i = 2 := by
    have h := congrArg ψ (f.sum_repr w)
    rw [hψ] at h
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [← h]
    apply Finset.sum_congr rfl; intro i _; ring
  refine ⟨hψw, ?_⟩
  intro h
  have h3 : ψ (f 3) * f.repr w 3 = 0 := by
    have hh := hψw
    rw [Fin.sum_univ_four] at hh
    simp only [hw0, hψ0, mul_zero, zero_add] at hh
    linear_combination hh - h
  exact (mul_ne_zero hψ3 hw3) h3

private theorem h4_neg_dot (f : Module.Basis (Fin 4) (ZMod p) U) {w : U}
    {ψ : Module.Dual (ZMod p) U} (h : ∑ i, ψ (f i) * f.repr w i = 2) :
    ∑ i, (if i = 1 then -(ψ (f i)) else ψ (f i)) *
        (if i = 1 then -(f.repr w i) else f.repr w i) = 2 := by
  rw [← h]
  apply Finset.sum_congr rfl; intro i _
  by_cases hi : i = 1 <;> simp [hi]

private theorem h4_conj_diagSignMat_one (f : Module.Basis (Fin 4) (ZMod p) U)
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) {h : U ≃ₗ[ZMod p] U}
    (hhmat : LinearMap.toMatrix f f (h : U →ₗ[ZMod p] U) = diagSignMat (1 : Fin 4)) :
    LinearMap.toMatrix f f
        ((h * Module.reflection hψ * h : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec (fun i => if i = 1 then -(f.repr w i) else f.repr w i)
        (fun j => if j = 1 then -(ψ (f j)) else ψ (f j)) := by
  rw [show ((h * Module.reflection hψ * h : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (h : U →ₗ[ZMod p] U) * (Module.reflection hψ : U →ₗ[ZMod p] U) *
        (h : U →ₗ[ZMod p] U) from rfl]
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hhmat, toMatrix_reflection f hψ]
  exact diagSignMat_one_conj_vecMulVec _ _

private theorem h4_exists_neg_one {α : ZMod p} (hα : α ^ 2 = α + 1)
    [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (f : Module.Basis (Fin 4) (ZMod p) U) (hH : basisClosure f (h3Mats α) ≤ G) {w : U}
    {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hb : Module.reflection hψ ∈ G)
    (hw0 : f.repr w 0 = 0) (hψ0 : ψ (f 0) = 0)
    (hψw : ∑ i, ψ (f i) * f.repr w i = 2) (k : Fin 3)
    (h11 : ψ (f 1) * f.repr w 1 = h4CandCoroot α k 1 * h4CandRoot α k 1)
    (h12 : (-1 : ZMod p) * (ψ (f 1) * f.repr w 2) =
      h4CandCoroot α k 1 * h4CandRoot α k 2)
    (h21 : (-1 : ZMod p) * (ψ (f 2) * f.repr w 1) =
      h4CandCoroot α k 2 * h4CandRoot α k 1)
    (h22 : ψ (f 2) * f.repr w 2 = h4CandCoroot α k 2 * h4CandRoot α k 2) :
    ∃ μ : (ZMod p)ˣ,
      basisClosure (f.unitsSMul (Function.update 1 (Fin.last 3) μ)) (h4BlockMats α) ≤ G := by
  obtain ⟨h, hhH, hhmat⟩ := exists_mem_h3Mats_refl hα f 0
  have hhmat' : LinearMap.toMatrix f f (h : U →ₗ[ZMod p] U) = diagSignMat (1 : Fin 4) := by
    rw [hhmat, ← h3ReflMat_0]
  let c : U ≃ₗ[ZMod p] U := h * Module.reflection hψ * h
  let ρ' : Fin 4 → ZMod p := fun i => if i = 1 then -(f.repr w i) else f.repr w i
  let κ' : Fin 4 → ZMod p := fun j => if j = 1 then -(ψ (f j)) else ψ (f j)
  have hcG : c ∈ G := G.mul_mem (G.mul_mem (hH hhH) hb) (hH hhH)
  have hcmat : LinearMap.toMatrix f f (c : U →ₗ[ZMod p] U) = 1 - Matrix.vecMulVec ρ' κ' := by
    change LinearMap.toMatrix f f
        ((h * Module.reflection hψ * h : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ρ' κ'
    exact h4_conj_diagSignMat_one f hψ hhmat'
  have hρ'0 : ρ' 0 = 0 := by simp [ρ', hw0]
  have hκ'0 : κ' 0 = 0 := by simp [κ', hψ0]
  have hκ'ρ' : ∑ i, κ' i * ρ' i = 2 := by
    simpa [ρ', κ'] using h4_neg_dot f hψw
  have h11' : κ' 1 * ρ' 1 = h4CandCoroot α k 1 * h4CandRoot α k 1 := by
    simpa [ρ', κ'] using h11
  have h12' : κ' 1 * ρ' 2 = h4CandCoroot α k 1 * h4CandRoot α k 2 := by
    simpa [ρ', κ', neg_mul] using h12
  have h21' : κ' 2 * ρ' 1 = h4CandCoroot α k 2 * h4CandRoot α k 1 := by
    simpa [ρ', κ', neg_mul, mul_neg] using h21
  have h22' : κ' 2 * ρ' 2 = h4CandCoroot α k 2 * h4CandRoot α k 2 := by
    simpa [ρ', κ'] using h22
  obtain ⟨μ, hμ⟩ := exists_toMatrix_unitsSMul_eq_h4CandMat hα f hcmat hρ'0 hκ'0 hκ'ρ' k
    h11' h12' h21' h22'
  exact ⟨μ, basisClosure_h4BlockMats_le hα f hH μ k hcG hμ⟩

theorem exists_basisClosure_h4BlockMats_le (hp5 : p ≠ 5) {α : ZMod p} (hα : α ^ 2 = α + 1)
    [Module.Finite (ZMod p) U] {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 5)
    (f : Module.Basis (Fin 4) (ZMod p) U) (hH : basisClosure f (h3Mats α) ≤ G) {w : U}
    {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hb : Module.reflection hψ ∈ G)
    (hw0 : f.repr w 0 = 0) (hψ0 : ψ (f 0) = 0) (hw3 : f.repr w 3 ≠ 0) (hψ3 : ψ (f 3) ≠ 0)
    (hw : f.repr w 1 ≠ 0 ∨ f.repr w 2 ≠ 0) :
    ∃ μ : (ZMod p)ˣ,
      basisClosure (f.unitsSMul (Function.update 1 (Fin.last 3) μ)) (h4BlockMats α) ≤ G := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hbmat : LinearMap.toMatrix f f (Module.reflection hψ : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec (fun i => f.repr w i) (fun i => ψ (f i)) :=
    toMatrix_reflection f hψ
  have hr := h3Refl_mem_ne_reflection f hH hα hψ hbmat hw3 hψ3
  have hc := h3EtaConstraints_of_toMatrix hp5 hα hG f hψ hb hw0 hψ0 hr
  obtain ⟨hψw, h2'⟩ := h4_psi_sum f hψ hw0 hψ0 hw3 hψ3
  obtain ⟨k, s, hs, h11, h12, h21, h22⟩ := H3EtaConstraints.exists_cand hp5 hα hc hw h2'
  rcases hs with hs | hs
  · subst hs
    have h11' : (fun i => ψ (f i)) 1 * (fun i => f.repr w i) 1 =
        h4CandCoroot α k 1 * h4CandRoot α k 1 := by simpa using h11
    have h12' : (fun i => ψ (f i)) 1 * (fun i => f.repr w i) 2 =
        h4CandCoroot α k 1 * h4CandRoot α k 2 := by
      have h := h12; rw [one_mul] at h; simpa using h
    have h21' : (fun i => ψ (f i)) 2 * (fun i => f.repr w i) 1 =
        h4CandCoroot α k 2 * h4CandRoot α k 1 := by
      have h := h21; rw [one_mul] at h; simpa using h
    have h22' : (fun i => ψ (f i)) 2 * (fun i => f.repr w i) 2 =
        h4CandCoroot α k 2 * h4CandRoot α k 2 := by simpa using h22
    obtain ⟨μ, hμ⟩ := exists_toMatrix_unitsSMul_eq_h4CandMat hα f hbmat hw0 hψ0 hψw k
      h11' h12' h21' h22'
    exact ⟨μ, basisClosure_h4BlockMats_le hα f hH μ k hb hμ⟩
  · subst hs
    exact h4_exists_neg_one hα f hH hψ hb hw0 hψ0 hψw k h11 h12 h21 h22

end CFSG.StandardType.ZS

end
