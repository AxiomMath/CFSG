module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.F2Fixed
public import CFSG.ClassicalGroups.Orthogonal.Basic
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Open QuadraticMap
open scoped Matrix MatrixGroups

@[expose] def levi2Left {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  Matrix.fromBlocks !![1, 0, 0; 0, M 0 0, 0; 0, 0, M 0 0] !![0, 0, 0; 0, 0, M 0 1; 0, M 0 1, 0]
    !![0, 0, 0; 0, 0, M 1 0; 0, M 1 0, 0] !![1, 0, 0; 0, M 1 1, 0; 0, 0, M 1 1]

@[expose] def levi2Right {K : Type} [Field K] (N : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  Matrix.fromBlocks !![1, 0, 0; 0, N 0 0, N 1 0; 0, N 0 1, N 1 1] 0 0
    !![1, 0, 0; 0, N 1 1, N 0 1; 0, N 1 0, N 0 0]

theorem levi2Left_one {K : Type} [Field K] :
    levi2Left (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi2Left, Matrix.one_apply]

theorem levi2Right_one {K : Type} [Field K] :
    levi2Right (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi2Right, Matrix.one_apply]

theorem levi2Left_mul {K : Type} [Field K] (M N : Matrix (Fin 2) (Fin 2) K) :
    levi2Left (M * N) = levi2Left M * levi2Left N := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi2Left, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      Fin.sum_univ_two] <;> ring

theorem levi2Right_mul {K : Type} [Field K] (M N : Matrix (Fin 2) (Fin 2) K) :
    levi2Right (M * N) = levi2Right N * levi2Right M := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi2Right, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      Fin.sum_univ_two] <;> ring

theorem levi2Left_mul_levi2Right {K : Type} [Field K] (M N : Matrix (Fin 2) (Fin 2) K) :
    levi2Left M * levi2Right N = levi2Right N * levi2Left M := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi2Left, levi2Right, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      Fin.sum_univ_two] <;> ring

theorem statedQuadPlus_three {K : Type} [Field K] (v : Fin 3 ⊕ Fin 3 → K) :
    StatedQuadPlus 3 K v =
      v (.inl 0) * v (.inr 0) + v (.inl 1) * v (.inr 1) + v (.inl 2) * v (.inr 2) := by
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_three]

theorem levi2Left_quad {K : Type} [Field K] [CharP K 2] (M : Matrix (Fin 2) (Fin 2) K)
    (hM : M.det = 1) (v : Fin 3 ⊕ Fin 3 → K) :
    StatedQuadPlus 3 K (levi2Left M *ᵥ v) = StatedQuadPlus 3 K v := by
  rw [Matrix.det_fin_two] at hM
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [statedQuadPlus_three, levi2Left, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_three]
  linear_combination (v (.inl 1) * v (.inr 1) + v (.inl 2) * v (.inr 2)) * hM +
    (M 0 1 * M 1 0 * (v (.inl 1) * v (.inr 1) + v (.inl 2) * v (.inr 2)) +
      M 0 0 * M 1 0 * v (.inl 1) * v (.inl 2) + M 0 1 * M 1 1 * v (.inr 1) * v (.inr 2)) * h2

theorem levi2Right_quad {K : Type} [Field K] [CharP K 2] (N : Matrix (Fin 2) (Fin 2) K)
    (hN : N.det = 1) (v : Fin 3 ⊕ Fin 3 → K) :
    StatedQuadPlus 3 K (levi2Right N *ᵥ v) = StatedQuadPlus 3 K v := by
  rw [Matrix.det_fin_two] at hN
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [statedQuadPlus_three, levi2Right, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_three]
  linear_combination (v (.inl 1) * v (.inr 1) + v (.inl 2) * v (.inr 2)) * hN +
    (N 0 1 * N 1 0 * (v (.inl 1) * v (.inr 1) + v (.inl 2) * v (.inr 2)) +
      N 0 0 * N 0 1 * v (.inl 1) * v (.inr 2) + N 1 0 * N 1 1 * v (.inl 2) * v (.inr 1)) * h2

theorem levi2Left_mulVec_fix {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    levi2Left M *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      levi2Left M *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
  constructor <;> funext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [levi2Left, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
      Pi.single_apply]

theorem levi2Right_mulVec_fix {K : Type} [Field K] (N : Matrix (Fin 2) (Fin 2) K) :
    levi2Right N *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 ∧
      levi2Right N *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 0) 1 := by
  constructor <;> funext i <;> rcases i with i | i <;> fin_cases i <;>
    simp [levi2Right, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
      Pi.single_apply]

theorem levi2Right_transpose_mul {K : Type} [Field K] (M N : Matrix (Fin 2) (Fin 2) K) :
    levi2Right (M * N)ᵀ = levi2Right Mᵀ * levi2Right Nᵀ := by
  rw [Matrix.transpose_mul, levi2Right_mul]

@[expose] def levi2Units {K : Type} [Field K]
    (f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (hf : ∀ M N, f (M * N) = f M * f N) (hf1 : f 1 = 1) (g : SL(2, K)) :
    GL (Fin 3 ⊕ Fin 3) K :=
  ⟨f (g : Matrix (Fin 2) (Fin 2) K), f ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K),
    by rw [← hf, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, hf1],
    by rw [← hf, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, hf1]⟩

@[expose] def leviLeftHom {K : Type} [Field K] : SL(2, K) →* GL (Fin 3 ⊕ Fin 3) K :=
  MonoidHom.mk' (levi2Units levi2Left levi2Left_mul levi2Left_one) fun g h =>
    Units.ext (by simp only [levi2Units, Units.val_mul, Units.val_mk,
      Matrix.SpecialLinearGroup.coe_mul]; exact levi2Left_mul _ _)

@[expose] def leviRightHom {K : Type} [Field K] : SL(2, K) →* GL (Fin 3 ⊕ Fin 3) K :=
  MonoidHom.mk' (levi2Units (fun M => levi2Right Mᵀ) levi2Right_transpose_mul
    (by simp [levi2Right_one])) fun g h =>
    Units.ext (by simp only [levi2Units, Units.val_mul, Units.val_mk,
      Matrix.SpecialLinearGroup.coe_mul]; exact levi2Right_transpose_mul _ _)

theorem leviLeftHom_val {K : Type} [Field K] (g : SL(2, K)) :
    (leviLeftHom g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      levi2Left (g : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem leviRightHom_val {K : Type} [Field K] (g : SL(2, K)) :
    (leviRightHom g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      levi2Right (g : Matrix (Fin 2) (Fin 2) K)ᵀ :=
  rfl

theorem mem_statedOmega_quadPlus_of_perfect {K : Type} [Field K] {G : Type} [Group G]
    [Group.IsPerfect G] (f : G →* GL (Fin 3 ⊕ Fin 3) K)
    (hf : ∀ (g : G) (v : Fin 3 ⊕ Fin 3 → K),
      StatedQuadPlus 3 K ((f g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) =
        StatedQuadPlus 3 K v) (g : G) :
    f g ∈ StatedOmega (StatedQuadPlus 3 K) := by
  have hle : f.range ≤ CFSG.MatrixModel.isometryCore (StatedQuadPlus 3 K) := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact Subgroup.subset_closure (fun v => hf x v)
  have hg : g ∈ commutator G := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top g
  have h := Subgroup.mem_map_of_mem f hg
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h
  exact Subgroup.commutator_mono hle hle h

@[expose] def levi2Diag {K : Type} [Field K] (α : K) (hα : α ≠ 0) : SL(2, K) :=
  ⟨!![α, 0; 0, α⁻¹], by rw [Matrix.det_fin_two_of]; simp [hα]⟩

theorem levi2Diag_val {K : Type} [Field K] (α : K) (hα : α ≠ 0) :
    (levi2Diag α hα : Matrix (Fin 2) (Fin 2) K) = !![α, 0; 0, α⁻¹] :=
  rfl

theorem statedQuadPlus_levi2Left_witness {K : Type} [Field K] (α : K) :
    StatedQuadPlus 3 K (levi2Left (!![α, 0; 0, α⁻¹] : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) +
      (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = (α + 1) * (α⁻¹ + 1) := by
  rw [statedQuadPlus_three]
  simp [levi2Left, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
    Pi.single_apply] <;> ring

theorem statedQuadPlus_levi2Right_witness {K : Type} [Field K] (α : K) :
    StatedQuadPlus 3 K (levi2Right (!![α, 0; 0, α⁻¹] : Matrix (Fin 2) (Fin 2) K)ᵀ *ᵥ
        (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) +
      (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1)) = (α + 1) * (α⁻¹ + 1) := by
  rw [statedQuadPlus_three]
  simp [levi2Right, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
    Pi.single_apply] <;> ring

theorem polar_levi_witness {K : Type} [Field K] :
    polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1)
      (Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1) = 0 := by
  simp [polar_quadPlus, Pi.single_apply]

theorem exists_levi_pair {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ∃ σ τ : SL(2, K) →* GL (Fin 3 ⊕ Fin 3) K,
      (∀ g, σ g ∈ StatedOmega (StatedQuadPlus 3 K)) ∧
      (∀ h, τ h ∈ StatedOmega (StatedQuadPlus 3 K)) ∧
      (∀ g h, σ g * τ h = τ h * σ g) ∧
      (∀ g, (σ g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ Pi.single (Sum.inl 0) 1 =
          Pi.single (Sum.inl 0) 1 ∧
        (σ g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ Pi.single (Sum.inr 0) 1 =
          Pi.single (Sum.inr 0) 1) ∧
      (∀ h, (τ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ Pi.single (Sum.inl 0) 1 =
          Pi.single (Sum.inl 0) 1 ∧
        (τ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ Pi.single (Sum.inr 0) 1 =
          Pi.single (Sum.inr 0) 1) ∧
      (∃ (g : SL(2, K)) (w : Fin 3 ⊕ Fin 3 → K),
        polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) w = 0 ∧
          quadPlus 3 K ((σ g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ w + w) ≠ 0) ∧
      (∃ (h : SL(2, K)) (w : Fin 3 ⊕ Fin 3 → K),
        polar (quadPlus 3 K) (Pi.single (Sum.inl 0) 1) w = 0 ∧
          quadPlus 3 K ((τ h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ w + w) ≠ 0) := by
  haveI : Group.IsPerfect (SL(2, K)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨α, hα0, hα2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K hK
  have hα1 : α ≠ 1 := fun h => hα2 (by rw [h]; norm_num)
  have hs1 : α + 1 ≠ 0 := fun h => hα1 (by linear_combination h - h2)
  have hs2 : α⁻¹ + 1 ≠ 0 := fun h => hα1 (inv_eq_one.mp (by linear_combination h - h2))
  refine ⟨leviLeftHom, leviRightHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    refine mem_statedOmega_quadPlus_of_perfect leviLeftHom (fun x v => ?_) g
    rw [leviLeftHom_val]
    exact levi2Left_quad _ (Matrix.SpecialLinearGroup.det_coe x) v
  · intro h
    refine mem_statedOmega_quadPlus_of_perfect leviRightHom (fun x v => ?_) h
    rw [leviRightHom_val]
    refine levi2Right_quad _ ?_ v
    rw [Matrix.det_transpose]
    exact Matrix.SpecialLinearGroup.det_coe x
  · intro g h
    apply Units.ext
    simp only [Units.val_mul, leviLeftHom_val, leviRightHom_val]
    exact levi2Left_mul_levi2Right _ _
  · intro g
    rw [leviLeftHom_val]
    exact levi2Left_mulVec_fix _
  · intro h
    rw [leviRightHom_val]
    exact levi2Right_mulVec_fix _
  · refine ⟨levi2Diag α hα0, Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1,
      polar_levi_witness, ?_⟩
    rw [leviLeftHom_val, levi2Diag_val, coe_quadPlus, statedQuadPlus_levi2Left_witness]
    exact mul_ne_zero hs1 hs2
  · refine ⟨levi2Diag α hα0, Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr 1) 1,
      polar_levi_witness, ?_⟩
    rw [leviRightHom_val, levi2Diag_val, coe_quadPlus, statedQuadPlus_levi2Right_witness]
    exact mul_ne_zero hs1 hs2

end CFSG.RankThree.GF2n.Stroth80
