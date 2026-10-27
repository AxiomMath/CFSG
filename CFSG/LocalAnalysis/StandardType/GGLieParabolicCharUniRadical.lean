module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

namespace GGUniRad

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private abbrev Mat : Type := Matrix (HypIndex r ε) (HypIndex r ε) K

private theorem uniRad_det_one_sub_of_isNilpotent
    {N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hN : IsNilpotent N) :
    (1 - N).det = 1 := by
  have h1 : N.charpoly = Polynomial.X ^ Fintype.card (HypIndex r ε) :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
  have h2 := Matrix.eval_charpoly N (1 : K)
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  exact h2.symm

private theorem uniRad_det_eq_one_of_sub_one_pow_three
    {M : Matrix (HypIndex r ε) (HypIndex r ε) K} (hM : (M - 1) ^ 3 = 0) : M.det = 1 := by
  have hN : IsNilpotent (1 - M) :=
    ⟨3, by rw [show (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) - M = -(M - 1) by abel,
      neg_pow, hM, mul_zero]⟩
  rw [← uniRad_det_one_sub_of_isNilpotent hN, sub_sub_cancel]

private theorem uniRad_eq_zero_of_forall_mulVec_eq_zero
    {N : Matrix (HypIndex r ε) (HypIndex r ε) K} (hN : ∀ v, N *ᵥ v = 0) : N = 0 := by
  ext i j
  have h1 := congrFun (hN (Pi.single j 1)) i
  rwa [mulVec_single_one, col_apply] at h1

private theorem uniRad_sub_one_pow_three_eq_zero
    {M : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hM : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) -
      (M *ᵥ (M *ᵥ v - v) - (M *ᵥ v - v)) = 0) : (M - 1) ^ 3 = 0 := by
  refine uniRad_eq_zero_of_forall_mulVec_eq_zero fun v => ?_
  rw [pow_three, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [sub_mulVec, one_mulVec]
  exact hM v

private noncomputable def uniRad_unipotentGL (M : Matrix (HypIndex r ε) (HypIndex r ε) K)
    (hM : (M - 1) ^ 3 = 0) : GL (HypIndex r ε) K where
  val := M
  inv := 1 - (M - 1) + (M - 1) ^ 2
  val_inv := by
    have h1 : M * (1 - (M - 1) + (M - 1) ^ 2) = 1 + (M - 1) ^ 3 := by noncomm_ring
    rw [h1, hM, add_zero]
  inv_val := by
    have h1 : (1 - (M - 1) + (M - 1) ^ 2) * M = 1 + (M - 1) ^ 3 := by noncomm_ring
    rw [h1, hM, add_zero]

private theorem uniRad_coe_unipotentGL (M : Matrix (HypIndex r ε) (HypIndex r ε) K)
    (hM : (M - 1) ^ 3 = 0) :
    ((uniRad_unipotentGL M hM : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = M :=
  rfl

private theorem uniRad_scalar_mulVec (c : K) (v : HypIndex r ε → K) :
    Matrix.scalar (HypIndex r ε) c *ᵥ v = c • v := by
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem uniRad_exists_hypForm_ne_zero (h : UnitaryFieldData p f K)
    {w : HypIndex r ε → K} (hw : w ≠ 0) : ∃ x, hypForm h r ε w x ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hw (hypForm_separatingLeft h w hall)

private noncomputable def uniRad_gramRow (h : UnitaryFieldData p f K)
    (w : HypIndex r ε → K) : HypIndex r ε → K :=
  (fun a => h.bar (w a)) ᵥ* hypGram r ε K

private theorem uniRad_gramRow_dotProduct (h : UnitaryFieldData p f K)
    (w v : HypIndex r ε → K) : uniRad_gramRow h w ⬝ᵥ v = hypForm h r ε w v := by
  rw [uniRad_gramRow, gramForm_apply, dotProduct_mulVec]

private noncomputable def uniRad_eichlerMatrix (h : UnitaryFieldData p f K)
    (w y : HypIndex r ε → K) (c : K) : Matrix (HypIndex r ε) (HypIndex r ε) K :=
  1 + vecMulVec y (uniRad_gramRow h w) - vecMulVec w (uniRad_gramRow h y) +
    c • vecMulVec w (uniRad_gramRow h w)

private theorem uniRad_eichlerMatrix_mulVec (h : UnitaryFieldData p f K)
    (w y : HypIndex r ε → K) (c : K) (v : HypIndex r ε → K) :
    uniRad_eichlerMatrix h w y c *ᵥ v =
      v + hypForm h r ε w v • y - hypForm h r ε y v • w +
        (c * hypForm h r ε w v) • w := by
  simp only [uniRad_eichlerMatrix, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec,
    vecMulVec_mulVec, uniRad_gramRow_dotProduct, op_smul_eq_smul, smul_smul]

private theorem uniRad_eichlerMatrix_isometry (h : UnitaryFieldData p f K)
    (hH : (hypForm h r ε).IsSymm) {w y : HypIndex r ε → K}
    (hww : hypForm h r ε w w = 0) (hwy : hypForm h r ε w y = 0) {c : K}
    (hc : c + h.bar c = -hypForm h r ε y y) (v v' : HypIndex r ε → K) :
    hypForm h r ε (uniRad_eichlerMatrix h w y c *ᵥ v) (uniRad_eichlerMatrix h w y c *ᵥ v') =
      hypForm h r ε v v' := by
  have hyw : hypForm h r ε y w = 0 := by rw [← hH.eq w y, hwy, map_zero]
  have hvy : hypForm h r ε v y = h.bar (hypForm h r ε y v) := (hH.eq y v).symm
  have hvw : hypForm h r ε v w = h.bar (hypForm h r ε w v) := (hH.eq w v).symm
  rw [uniRad_eichlerMatrix_mulVec, uniRad_eichlerMatrix_mulVec]
  simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hww, hwy, hyw, hvy, hvw, map_mul]
  linear_combination (h.bar (hypForm h r ε w v) * hypForm h r ε w v') * hc

private theorem uniRad_eichlerMatrix_sub_one_pow_three (h : UnitaryFieldData p f K)
    (hH : (hypForm h r ε).IsSymm) {w y : HypIndex r ε → K}
    (hww : hypForm h r ε w w = 0) (hwy : hypForm h r ε w y = 0) (c : K) :
    (uniRad_eichlerMatrix h w y c - 1) ^ 3 = 0 := by
  have hyw : hypForm h r ε y w = 0 := by rw [← hH.eq w y, hwy, map_zero]
  refine uniRad_sub_one_pow_three_eq_zero fun v => ?_
  simp only [uniRad_eichlerMatrix_mulVec, map_add, map_sub, map_smul, smul_eq_mul, hww, hwy, hyw]
  simp only [mul_zero, zero_smul, sub_zero, add_zero, zero_mul, sub_self]

private theorem uniRad_eichlerGL_mem (h : UnitaryFieldData p f K) (hH : (hypForm h r ε).IsSymm)
    {w y : HypIndex r ε → K} (hww : hypForm h r ε w w = 0) (hwy : hypForm h r ε w y = 0)
    {c : K} (hc : c + h.bar c = -hypForm h r ε y y) :
    uniRad_unipotentGL (uniRad_eichlerMatrix h w y c)
      (uniRad_eichlerMatrix_sub_one_pow_three h hH hww hwy c) ∈ hypSU h r ε :=
  mem_gramSU_iff_isometry.mpr ⟨fun v v' => uniRad_eichlerMatrix_isometry h hH hww hwy hc v v',
    uniRad_det_eq_one_of_sub_one_pow_three
      (uniRad_eichlerMatrix_sub_one_pow_three h hH hww hwy c)⟩

private theorem uniRad_eichlerHyp_mem (h : UnitaryFieldData p f K) (hH : (hypForm h r ε).IsSymm)
    {w y : HypIndex r ε → K} (hww : hypForm h r ε w w = 0) (hwy : hypForm h r ε w y = 0)
    {c : K} (hc : c + h.bar c = -hypForm h r ε y y) :
    ∃ e : hypSU h r ε,
      ((e : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        uniRad_eichlerMatrix h w y c := by
  refine ⟨⟨uniRad_unipotentGL (uniRad_eichlerMatrix h w y c)
    (uniRad_eichlerMatrix_sub_one_pow_three h hH hww hwy c),
    uniRad_eichlerGL_mem h hH hww hwy hc⟩, ?_⟩
  exact uniRad_coe_unipotentGL (uniRad_eichlerMatrix h w y c)
    (uniRad_eichlerMatrix_sub_one_pow_three h hH hww hwy c)

private theorem uniRad_mulVec_mem_of_smul_eq {W : Submodule K (HypIndex r ε → K)}
    {g : GL (HypIndex r ε) K} (hg : g • W = W) :
    ∀ v ∈ W, (g : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ W := by
  intro v hv
  have h : g • v ∈ g • W := (Submodule.mem_smul_pointwise_iff_exists _ g W).mpr ⟨v, hv, rfl⟩
  rw [hg] at h
  exact h

private theorem uniRad_mulVec_mem_of_mem_isoStabilizer (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex r ε → K)} {g : hypSU h r ε}
    (hg : g ∈ isoStabilizer h r ε W) :
    ∀ v ∈ W, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ W := by
  have hgW : (g : GL (HypIndex r ε) K) • W = W := by
    rw [← Subgroup.smul_def]
    exact mem_isoStabilizer.mp hg
  exact uniRad_mulVec_mem_of_smul_eq hgW

private theorem uniRad_mulVec_perp_of_mem_isoStabilizer (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex r ε → K)} {g : hypSU h r ε}
    (hg : g ∈ isoStabilizer h r ε W) :
    ∀ y ∈ W.orthogonalBilin (hypForm h r ε),
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y ∈
        W.orthogonalBilin (hypForm h r ε) := by
  intro y hy
  rw [Submodule.mem_orthogonalBilin] at hy ⊢
  intro w hw
  have hginv : g⁻¹ ∈ isoStabilizer h r ε W := (isoStabilizer h r ε W).inv_mem hg
  have h1 : ((((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ w ∈ W :=
    uniRad_mulVec_mem_of_mem_isoStabilizer h hginv w hw
  have hGw : (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      ((((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w)) = w := by
    rw [Subgroup.coe_inv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  calc hypForm h r ε w
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y)
      = hypForm h r ε
          (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
            ((((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
              Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w))
          (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) := by
            rw [hGw]
    _ = hypForm h r ε
          ((((g⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w) y :=
          (mem_gramSU_iff_isometry.mp g.2).1 _ _
    _ = 0 := hy _ h1

@[expose] def uniRadical (h : UnitaryFieldData p f K) (r ε : ℕ)
    (W : Submodule K (HypIndex r ε → K)) : Subgroup (hypSU h r ε) where
  carrier := {g | (∀ w ∈ W,
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w = w) ∧
    ∀ y ∈ W.orthogonalBilin (hypForm h r ε),
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y ∈ W}
  one_mem' := ⟨fun w _ => by rw [OneMemClass.coe_one, Units.val_one, one_mulVec],
    fun y _ => by
      rw [OneMemClass.coe_one, Units.val_one, one_mulVec, sub_self]
      exact zero_mem _⟩
  mul_mem' := by
    intro g g' hg hg'
    obtain ⟨h1, h2⟩ := hg
    obtain ⟨h1', h2'⟩ := hg'
    refine ⟨fun w hw => ?_, fun y hy => ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, h1' w hw, h1 w hw]
    · have hy' : (((g' : GL (HypIndex r ε) K)) : Mat) *ᵥ y - y ∈ W := h2' y hy
      have hmy : (((g : GL (HypIndex r ε) K)) : Mat) *ᵥ y - y ∈ W := h2 y hy
      have hmy' : (((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
          ((((g' : GL (HypIndex r ε) K)) : Mat) *ᵥ y - y) ∈ W := by
        rw [h1 _ hy']; exact hy'
      have heq : ((((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (((g' : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ y - y =
          (((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
            ((((g' : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y) +
          ((((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y) := by
        rw [mulVec_sub, mulVec_mulVec]
        abel
      rw [Subgroup.coe_mul, Units.val_mul, heq]
      exact add_mem hmy' hmy
  inv_mem' := by
    intro g hg
    obtain ⟨h1, h2⟩ := hg
    have hMM : (((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hMM' : ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *
        (((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hfix : ∀ w ∈ W,
        ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ w = w := by
      intro w hw
      calc ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ w
          = ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ
              (((g : GL (HypIndex r ε) K) : Mat) *ᵥ w) := by rw [h1 w hw]
        _ = w := by rw [mulVec_mulVec, hMM', one_mulVec]
    refine ⟨fun w hw => ?_, fun y hy => ?_⟩
    · rw [Subgroup.coe_inv]
      exact hfix w hw
    · have h2y : (((g : GL (HypIndex r ε) K)) : Mat) *ᵥ y - y ∈ W := h2 y hy
      have hmem : ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ
          ((((g : GL (HypIndex r ε) K)) : Mat) *ᵥ y - y) ∈ W := by
        rw [hfix _ h2y]; exact h2y
      have heq : ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ y - y =
          -(((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ
            ((((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y)) := by
        rw [mulVec_sub, mulVec_mulVec, hMM', one_mulVec]
        abel
      rw [Subgroup.coe_inv, heq]
      exact neg_mem hmem

theorem mem_uniRadical {h : UnitaryFieldData p f K} {W : Submodule K (HypIndex r ε → K)}
    {g : hypSU h r ε} :
    g ∈ uniRadical h r ε W ↔ (∀ w ∈ W,
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w = w) ∧
    ∀ y ∈ W.orthogonalBilin (hypForm h r ε),
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y ∈ W :=
  Iff.rfl

private theorem uniRad_eichlerHyp_mem_uniRadical (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex r ε → K)}
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, hypForm h r ε v w = 0) {w y : HypIndex r ε → K} (hw : w ∈ W)
    (hy : y ∈ W.orthogonalBilin (hypForm h r ε)) {c : K}
    (hc : c + h.bar c = -hypForm h r ε y y) :
    ∃ e ∈ uniRadical h r ε W,
      ((e : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        uniRad_eichlerMatrix h w y c := by
  obtain ⟨e, he⟩ := uniRad_eichlerHyp_mem h (hypForm_isSymm h) (hWiso w hw w hw)
    (Submodule.mem_orthogonalBilin.mp hy w hw) hc
  refine ⟨e, ?_, he⟩
  rw [mem_uniRadical]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [he, uniRad_eichlerMatrix_mulVec, hWiso w hw v hv]
    have hyv : hypForm h r ε y v = 0 := by
      rw [← (hypForm_isSymm h).eq v y, Submodule.mem_orthogonalBilin.mp hy v hv, map_zero]
    rw [hyv]
    simp
  · rw [he]
    have key : uniRad_eichlerMatrix h w y c *ᵥ v - v = -(hypForm h r ε y v • w) := by
      rw [uniRad_eichlerMatrix_mulVec, Submodule.mem_orthogonalBilin.mp hv w hw, zero_smul,
        add_zero, mul_zero, zero_smul, add_zero]
      abel
    rw [key]
    exact neg_mem (Submodule.smul_mem _ _ hw)

theorem uniRadical_le_isoStabilizer (h : UnitaryFieldData p f K)
    (W : Submodule K (HypIndex r ε → K)) :
    uniRadical h r ε W ≤ isoStabilizer h r ε W := by
  intro g hg
  rw [mem_isoStabilizer, Subgroup.smul_def]
  refine smul_eq_of_mulVec_mem ?_ ?_
  · intro v hv
    rw [(mem_uniRadical.mp hg).1 v hv]
    exact hv
  · intro v hv
    have hv' : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = v :=
      (mem_uniRadical.mp hg).1 v hv
    have h1 : ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ v = v := by
      calc ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ v
          = ((((g : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
              Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ
              (((g : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v := by
                rw [hv']
        _ = v := by
            rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [h1]
    exact hv

theorem uniRadical_normal (h : UnitaryFieldData p f K) (W : Submodule K (HypIndex r ε → K)) :
    ((uniRadical h r ε W).subgroupOf (isoStabilizer h r ε W)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  rw [mem_uniRadical] at hn ⊢
  obtain ⟨hn1, hn2⟩ := hn
  set Sg : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hSg
  set Sn : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    (((n : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hSn
  set Sgi : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    ((((g : hypSU h r ε) : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)
      with hSgi
  have hn1' : ∀ w ∈ W, Sn *ᵥ w = w := by
    intro w hw; simpa only [hSn] using hn1 w hw
  have hn2' : ∀ y ∈ W.orthogonalBilin (hypForm h r ε), Sn *ᵥ y - y ∈ W := by
    intro y hy; simpa only [hSn] using hn2 y hy
  have hgmem : ∀ v ∈ W, Sg *ᵥ v ∈ W := by
    intro v hv; simpa only [hSg] using uniRad_mulVec_mem_of_mem_isoStabilizer h g.2 v hv
  have hgimem : ∀ v ∈ W, Sgi *ᵥ v ∈ W := by
    intro v hv
    have hh := uniRad_mulVec_mem_of_mem_isoStabilizer h
      ((isoStabilizer h r ε W).inv_mem g.2) v hv
    simpa only [hSgi, Subgroup.coe_inv] using hh
  have hgiperp : ∀ y ∈ W.orthogonalBilin (hypForm h r ε), Sgi *ᵥ y ∈
      W.orthogonalBilin (hypForm h r ε) := by
    intro y hy
    have hh := uniRad_mulVec_perp_of_mem_isoStabilizer h
      ((isoStabilizer h r ε W).inv_mem g.2) y hy
    simpa only [hSgi, Subgroup.coe_inv] using hh
  have hcoe : ((((g * n * g⁻¹ : isoStabilizer h r ε W) : hypSU h r ε) :
      GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = Sg * Sn * Sgi := by
    simp only [hSg, hSn, hSgi, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  refine ⟨fun w hw => ?_, fun y hy => ?_⟩
  · rw [hcoe, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [show Sn *ᵥ (Sgi *ᵥ w) = Sgi *ᵥ w from hn1' _ (hgimem w hw)]
    rw [show Sg *ᵥ (Sgi *ᵥ w) = w from by
      rw [hSg, hSgi, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]]
  · rw [hcoe, ← mulVec_mulVec, ← mulVec_mulVec]
    have hper : Sn *ᵥ (Sgi *ᵥ y) - Sgi *ᵥ y ∈ W := hn2' _ (hgiperp y hy)
    have hmap : Sg *ᵥ (Sn *ᵥ (Sgi *ᵥ y) - Sgi *ᵥ y) ∈ W := hgmem _ hper
    have hgg : Sg *ᵥ (Sgi *ᵥ y) = y := by
      rw [hSg, hSgi, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have heq : Sg *ᵥ (Sn *ᵥ (Sgi *ᵥ y)) - y = Sg *ᵥ (Sn *ᵥ (Sgi *ᵥ y) - Sgi *ᵥ y) := by
      rw [mulVec_sub, hgg]
    rw [heq]
    exact hmap

theorem isPGroup_uniRadical (h : UnitaryFieldData p f K) (W : Submodule K (HypIndex r ε → K)) :
    IsPGroup p (uniRadical h r ε W) := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
    OneMemClass.coe_one, OneMemClass.coe_one, Units.val_one]
  set G := ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hG
  have hiso : ∀ x y, hypForm h r ε (G *ᵥ x) (G *ᵥ y) = hypForm h r ε x y := by
    intro x y
    have := (mem_gramSU_iff_isometry.mp (g : hypSU h r ε).2).1 x y
    simpa only [hG] using this
  have hfix : ∀ w ∈ W, G *ᵥ w = w := (mem_uniRadical.mp g.2).1
  have hperp : ∀ y ∈ W.orthogonalBilin (hypForm h r ε), G *ᵥ y - y ∈ W :=
    (mem_uniRadical.mp g.2).2
  have hout : ∀ v, G *ᵥ v - v ∈ W.orthogonalBilin (hypForm h r ε) := by
    intro v
    rw [Submodule.mem_orthogonalBilin]
    intro w hw
    rw [map_sub, ← hiso w v, hfix w hw, sub_self]
  have hN3 : (G - 1) ^ 3 = 0 := by
    refine uniRad_sub_one_pow_three_eq_zero fun v => ?_
    rw [hfix _ (hperp _ (hout v)), sub_self]
  have hp2 : G ^ (p ^ 2) = 1 := by
    obtain ⟨r', hr'⟩ := Commute.exists_add_pow_prime_pow_eq h.prime (Commute.one_left (G - 1)) 2
    have hp0 : ((p : ℕ) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 0 := by
      haveI : CharP K p := h.charP
      rw [← Matrix.diagonal_natCast p, CharP.cast_eq_zero K p, Matrix.diagonal_zero]
    have hNnil : (G - 1) ^ (p ^ 2) = 0 := by
      have hp2ge : 3 ≤ p ^ 2 := by nlinarith [h.prime.two_le]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp2ge
      rw [hk, pow_add, hN3, zero_mul]
    rw [add_sub_cancel] at hr'
    simp only [one_pow, hNnil, hp0, zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add] at hr'
    exact hr'
  simpa only [hG] using hp2

theorem exists_scalar_mul_mem_uniRadical (h : UnitaryFieldData p f K)
    {W : Submodule K (HypIndex r ε → K)} (h0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h r ε x y = 0) {s : hypSU h r ε}
    (hs : s ∈ isoStabilizer h r ε W)
    (hc : ∀ u ∈ uniRadical h r ε W, s * u * s⁻¹ * u⁻¹ ∈ hypScalars h r ε) :
    ∃ z ∈ hypScalars h r ε, ∃ q ∈ uniRadical h r ε W, s = z * q := by
  have hH : (hypForm h r ε).IsSymm := hypForm_isSymm h
  set S := ((s : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hS
  have hisoS : ∀ x y, hypForm h r ε (S *ᵥ x) (S *ᵥ y) = hypForm h r ε x y := by
    intro x y
    have := (mem_gramSU_iff_isometry.mp s.2).1 x y
    simpa only [hS] using this
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨x₀, hx₀⟩ := uniRad_exists_hypForm_ne_zero h hw₀0
  have hScomm : ∀ u ∈ uniRadical h r ε W, ∀ v,
      S *ᵥ (((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) =
        (((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (S *ᵥ v)) := by
    intro u hu v
    obtain ⟨c₀, -, -, hc₀mat⟩ := mem_normOneScalars.mp (hc u hu)
    set U : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hU
    set Uinv : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      (((u : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) with hUinv
    set Sinv : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      (((s : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) with hSinv
    have hcoh : (((s * u * s⁻¹ * u⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) = S * U * Sinv * Uinv := by
      simp only [hS, hU, hSinv, hUinv, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    have hUinvw : Uinv *ᵥ w₀ = w₀ := by
      have h1 : U *ᵥ w₀ = w₀ := (mem_uniRadical.mp hu).1 w₀ hw₀
      calc Uinv *ᵥ w₀ = Uinv *ᵥ (U *ᵥ w₀) := by rw [h1]
        _ = w₀ := by
            rw [hU, hUinv, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
              one_mulVec]
    have hSinvw : Sinv *ᵥ w₀ ∈ W := by
      have h1 : ((((s⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) *ᵥ w₀ ∈ W :=
        uniRad_mulVec_mem_of_mem_isoStabilizer h ((isoStabilizer h r ε W).inv_mem hs) w₀ hw₀
      simpa only [hSinv, Subgroup.coe_inv] using h1
    have hUfix : U *ᵥ (Sinv *ᵥ w₀) = Sinv *ᵥ w₀ := (mem_uniRadical.mp hu).1 _ hSinvw
    have hSSinv : S *ᵥ (Sinv *ᵥ w₀) = w₀ := by
      rw [hS, hSinv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hc0w : ((GeneralLinearGroup.scalar (HypIndex r ε) c₀ : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w₀ = w₀ := by
      rw [← hc₀mat, hcoh]
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hUinvw, hUfix, hSSinv]
    have hc0 : (c₀ : K) • w₀ = w₀ := by
      rw [← uniRad_scalar_mulVec (c₀ : K) w₀, ← GeneralLinearGroup.coe_scalar]
      exact hc0w
    have hc01 : c₀ = 1 := by
      have h' : ((c₀ : K) - 1) • w₀ = 0 := by rw [sub_smul, one_smul, hc0, sub_self]
      rcases (smul_eq_zero.mp h') with h'' | h''
      · exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp h'')
      · exact absurd h'' hw₀0
    have hz1mat : S * U * Sinv * Uinv = 1 := by
      rw [← hcoh, hc₀mat, hc01]
      simp
    have hz1 : s * u * s⁻¹ * u⁻¹ = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hcoh]
      exact hz1mat
    have hsu : s * u = u * s := by
      have h1 : s * u * s⁻¹ * u⁻¹ * (u * s) = u * s := by rw [hz1, one_mul]
      calc s * u = s * u * s⁻¹ * u⁻¹ * (u * s) := by group
        _ = u * s := h1
    have hSU : S * U = U * S := by
      have := congrArg (fun x : hypSU h r ε =>
        (((x : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K)) hsu
      simpa only [hS, hU, Subgroup.coe_mul, Units.val_mul] using this
    rw [mulVec_mulVec, mulVec_mulVec, hSU]
  have htrans : ∀ w ∈ W, ∀ v, hypForm h r ε w v • S *ᵥ w =
      hypForm h r ε w (S *ᵥ v) • w := by
    intro w hw v
    obtain ⟨τ, hτ, hτ0⟩ := h.exists_mem_traceZero_ne_zero
    have hτ' : τ + h.bar τ = 0 := h.mem_traceZero.mp hτ
    have hcτ : τ + h.bar τ = -hypForm h r ε 0 0 := by rw [hτ']; simp
    obtain ⟨t, ht, htmat⟩ := uniRad_eichlerHyp_mem_uniRadical h hW hw (zero_mem _) hcτ
    have htv : ∀ v, (((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) =
        v + (τ * hypForm h r ε w v) • w := by
      intro v
      rw [htmat, uniRad_eichlerMatrix_mulVec]
      simp
    have h1 := hScomm t ht v
    rw [htv, htv] at h1
    simp only [mulVec_add, mulVec_smul] at h1
    have h2 : (τ * hypForm h r ε w v) • S *ᵥ w =
        (τ * hypForm h r ε w (S *ᵥ v)) • w := add_left_cancel h1
    rw [mul_smul, mul_smul] at h2
    calc hypForm h r ε w v • S *ᵥ w
        = τ⁻¹ • (τ • (hypForm h r ε w v • S *ᵥ w)) := by
          rw [smul_smul, inv_mul_cancel₀ hτ0, one_smul]
      _ = τ⁻¹ • (τ • (hypForm h r ε w (S *ᵥ v) • w)) := by rw [h2]
      _ = hypForm h r ε w (S *ᵥ v) • w := by
          rw [smul_smul, inv_mul_cancel₀ hτ0, one_smul]
  have hline : ∀ w ∈ W, ∃ c : K, S *ᵥ w = c • w := by
    intro w hw
    by_cases hw0 : w = 0
    · exact ⟨0, by rw [hw0, mulVec_zero, smul_zero]⟩
    obtain ⟨x, hx⟩ := uniRad_exists_hypForm_ne_zero h hw0
    refine ⟨(hypForm h r ε w x)⁻¹ * hypForm h r ε w (S *ᵥ x), ?_⟩
    rw [mul_smul, ← htrans w hw x, smul_smul, inv_mul_cancel₀ hx, one_smul]
  have hmaps : ∀ w ∈ W, S.mulVecLin w ∈ W := by
    intro w hw
    obtain ⟨c, hc'⟩ := hline w hw
    rw [Matrix.mulVecLin_apply, hc']
    exact W.smul_mem c hw
  obtain ⟨μ, hμ⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := S.mulVecLin.restrict hmaps) fun w => by
      obtain ⟨c, hc'⟩ := hline w w.2
      rw [LinearIndependent.pair_iff]
      push Not
      refine ⟨c, -1, ?_, by norm_num⟩
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul, LinearMap.coe_restrict_apply,
        Matrix.mulVecLin_apply, hc', ZeroMemClass.coe_zero]
      rw [neg_one_smul, add_neg_cancel]
  have hAW : ∀ w ∈ W, S *ᵥ w = μ • w := by
    intro w hw
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hμ ⟨w, hw⟩)
    simpa using h1
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h1 := hAW w₀ hw₀
    rw [zero_smul] at h1
    apply hw₀0
    have h2 : ((((s : GL (HypIndex r ε) K)⁻¹ : GL (HypIndex r ε) K) : Mat)) *ᵥ
        (S *ᵥ w₀) = w₀ := by
      rw [hS, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    rw [← h2, h1, mulVec_zero]
  have hAv : ∀ v, μ * hypForm h r ε w₀ v = hypForm h r ε w₀ (S *ᵥ v) := by
    intro v
    have h1 := htrans w₀ hw₀ v
    rw [hAW w₀ hw₀, smul_smul] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← sub_smul] at h2
    have h3 := sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw₀0)
    rw [mul_comm] at h3
    exact h3
  have hN : h.norm μ = 1 := by
    have h1 := hisoS w₀ x₀
    rw [hAW w₀ hw₀, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← hAv x₀, ← mul_assoc] at h1
    rw [UnitaryFieldData.norm, mul_comm]
    exact mul_right_cancel₀ hx₀ (h1.trans (one_mul _).symm)
  set u : Kˣ := Units.mk0 μ hμ0 with hu
  set A' := GeneralLinearGroup.scalar (HypIndex r ε) u⁻¹ * s with hA'def
  have hA'v : ∀ v, (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = μ⁻¹ • (S *ᵥ v) := by
    intro v
    rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, ← mulVec_mulVec,
      uniRad_scalar_mulVec, hu, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hA'W : ∀ w ∈ W, (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w = w := by
    intro w hw
    rw [hA'v, hAW w hw, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have hNinv : h.bar μ⁻¹ * μ⁻¹ = 1 := by
    have h1 : h.bar μ * μ = 1 := by rw [mul_comm]; exact hN
    rw [map_inv₀, ← mul_inv, h1, inv_one]
  have hA'iso : ∀ x y, hypForm h r ε ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x)
      ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) = hypForm h r ε x y := by
    intro x y
    rw [hA'v, hA'v]
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [hisoS, ← mul_assoc, mul_comm μ⁻¹, hNinv, one_mul]
  have hA'comm : ∀ g ∈ uniRadical h r ε W, ∀ v,
      (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) =
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
          ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)) := by
    intro g hg v
    rw [hA'v, hA'v, hScomm g hg v, mulVec_smul]
  have hA'L : ∀ v, (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v - v ∈
      W.orthogonalBilin (hypForm h r ε) := by
    intro v
    refine Submodule.mem_orthogonalBilin.mpr fun w hw => ?_
    rw [map_sub, ← hA'iso w v, hA'W w hw, sub_self]
  have hA'LW : ∀ y ∈ W.orthogonalBilin (hypForm h r ε),
      (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y ∈ W := by
    intro y hy
    have hyy : -hypForm h r ε y y ∈ h.fixedField := by
      refine neg_mem (h.mem_fixedField.mpr ?_)
      exact hH.eq y y
    obtain ⟨c, hc'⟩ := h.traceLin_surjective ⟨_, hyy⟩
    have hc'' : c + h.bar c = -hypForm h r ε y y := congrArg Subtype.val hc'
    obtain ⟨E, hErad, hEmat⟩ := uniRad_eichlerHyp_mem_uniRadical h hW hw₀ hy hc''
    have h1 := hA'comm E hErad x₀
    rw [hEmat] at h1
    have ha' : hypForm h r ε w₀ ((A' : Mat) *ᵥ x₀) = hypForm h r ε w₀ x₀ := by
      rw [← hA'iso w₀ x₀, hA'W w₀ hw₀]
    rw [uniRad_eichlerMatrix_mulVec, uniRad_eichlerMatrix_mulVec, ha', mulVec_add, mulVec_sub,
      mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, hA'W w₀ hw₀] at h1
    have h2 : hypForm h r ε w₀ x₀ • ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y) =
        (hypForm h r ε y x₀ - hypForm h r ε y ((A' : Mat) *ᵥ x₀)) • w₀ := by
      rw [smul_sub, sub_smul]
      linear_combination (norm := module) h1
    have h3 : (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y - y =
        ((hypForm h r ε w₀ x₀)⁻¹ * (hypForm h r ε y x₀ -
          hypForm h r ε y ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x₀))) • w₀ := by
      rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hx₀, one_smul]
    rw [h3]
    exact W.smul_mem _ hw₀
  have hA'3 : ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) - 1) ^ 3 = 0 := by
    refine uniRad_sub_one_pow_three_eq_zero fun v => ?_
    rw [hA'W _ (hA'LW ((A' : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v - v) (hA'L v)), sub_self]
  have hA'SU : A' ∈ hypSU h r ε :=
    mem_gramSU_iff_isometry.mpr ⟨hA'iso, uniRad_det_eq_one_of_sub_one_pow_three hA'3⟩
  have hA'mat : (A' : Matrix (HypIndex r ε) (HypIndex r ε) K) = μ⁻¹ • S := by
    rw [hA'def, Units.val_mul, GeneralLinearGroup.coe_scalar, hS, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, hu, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hdetS : S.det = 1 := by
    have := (mem_gramSU_iff_isometry.mp s.2).2
    simpa only [hS] using this
  have hdetA' : (A' : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 :=
    uniRad_det_eq_one_of_sub_one_pow_three hA'3
  have hmu : μ ^ Fintype.card (HypIndex r ε) = 1 := by
    have h : (μ ^ Fintype.card (HypIndex r ε))⁻¹ = 1 := by
      rw [hA'mat, Matrix.det_smul, hdetS, mul_one] at hdetA'
      simpa only [inv_pow] using hdetA'
    rwa [inv_eq_one] at h
  have hcard : Fintype.card (HypIndex r ε) = 2 * r + ε := by
    simp [HypIndex, Fintype.card_sum, Fintype.card_fin]
    omega
  have hmu' : μ ^ (2 * r + ε) = 1 := by rwa [hcard] at hmu
  have hNu : h.norm (u : K) = 1 := by rw [hu, Units.val_mk0]; exact hN
  have hu' : u ^ (2 * r + ε) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, Units.val_one]
    exact hmu'
  have hzSU : GeneralLinearGroup.scalar (HypIndex r ε) u ∈ hypSU h r ε := by
    rw [mem_gramSU_iff_isometry]
    refine ⟨fun x y => ?_, ?_⟩
    · rw [GeneralLinearGroup.coe_scalar, uniRad_scalar_mulVec, uniRad_scalar_mulVec]
      simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, map_mul]
      rw [hu, Units.val_mk0]
      rw [← mul_assoc, show μ * h.bar μ = 1 by change h.norm μ = 1; exact hN, one_mul]
    · rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      simp only [Finset.prod_const, Finset.card_univ, hcard]
      rw [← Units.val_pow_eq_pow_val u (2 * r + ε), hu', Units.val_one]
  have hz : (⟨GeneralLinearGroup.scalar (HypIndex r ε) u, hzSU⟩ : hypSU h r ε) ∈
      hypScalars h r ε :=
    mem_normOneScalars.mpr ⟨u, hNu, hu', rfl⟩
  have hq : (⟨A', hA'SU⟩ : hypSU h r ε) ∈ uniRadical h r ε W := by
    rw [mem_uniRadical]
    exact ⟨hA'W, hA'LW⟩
  have hsq : S = Matrix.scalar (HypIndex r ε) (u : K) * (A' : Mat) := by
    rw [hA'mat, hu, Units.val_mk0, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
      smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  refine ⟨⟨GeneralLinearGroup.scalar (HypIndex r ε) u, hzSU⟩, hz, ⟨A', hA'SU⟩, hq, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul]
  exact hsq

end GGUniRad

end CFSG.StandardType
