module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightDefs
import CFSG.ClassicalInvolution.Phan.Standard
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
import CFSG.LieType.Chevalley.E6GraphLeviTheta
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowOverlapModel
import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveOrbit
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveRigid
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTw
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups
open CFSG.LieType.SeitzGeneration.ExcHigh

private def su6CutA {K : Type} [Field K] (ζ : K) : Matrix (Fin 2) (Fin 2) K :=
  !![ζ, ζ ^ 2; 1, 1]

private def su6CutN {K : Type} [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 1, 0]

private theorem su6Cut_zeta_sq {K : Type} [Field K] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 2 = ζ + 1 := by
  linear_combination hζ - (ζ + 1) * h2

private theorem su6Cut_zeta_cube {K : Type} [Field K] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 3 = 1 := by
  have hsq := su6Cut_zeta_sq h2 hζ
  calc ζ ^ 3 = ζ * ζ ^ 2 := by ring
    _ = ζ * (ζ + 1) := by rw [hsq]
    _ = ζ ^ 2 + ζ := by ring
    _ = (ζ + 1) + ζ := by rw [hsq]
    _ = 1 := by linear_combination ζ * h2

private theorem su6Cut_zeta_pow_four {K : Type} [Field K] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 4 = ζ := by
  have h3 := su6Cut_zeta_cube h2 hζ
  calc ζ ^ 4 = ζ ^ 3 * ζ := by ring
    _ = ζ := by rw [h3, one_mul]

private theorem su6Cut_sigma_zeta {K : Type} [Field K] (h2 : (2 : K) = 0) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : σ ζ = ζ ^ 2 := by
  have h3 := su6Cut_zeta_cube h2 hζ
  rw [hσ]
  calc ζ ^ 8 = ζ ^ (3 * 2 + 2) := by norm_num
    _ = ζ ^ (3 * 2) * ζ ^ 2 := by rw [pow_add]
    _ = (ζ ^ 3) ^ 2 * ζ ^ 2 := by rw [pow_mul]
    _ = ζ ^ 2 := by rw [h3]; simp

private theorem su6Cut_A_sigma {K : Type} [Field K] {σ : K ≃+* K} {ζ : K}
    (hσζ : σ ζ = ζ ^ 2) (hζ4 : ζ ^ 4 = ζ) :
    (su6CutA ζ).map σ.toRingHom = su6CutA ζ * su6CutN := by
  have hζ4' : (ζ ^ 2) ^ 2 = ζ := by
    rw [show (ζ ^ 2) ^ 2 = ζ ^ 4 by ring]
    exact hζ4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su6CutA, su6CutN, Matrix.mul_apply, Fin.sum_univ_two, hσζ, hζ4']

private theorem su6Cut_AtNA {K : Type} [Field K] {ζ : K} (h2 : (2 : K) = 0)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Matrix.transpose (su6CutA ζ) * su6CutN * su6CutA ζ = su6CutN := by
  have hsq := su6Cut_zeta_sq h2 hζ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su6CutA, su6CutN, Matrix.mul_apply, Fin.sum_univ_two, hsq]
  all_goals
    first
    | rw [← two_mul, h2, zero_mul]
    | linear_combination ζ * h2

private theorem su6Cut_frameLangSL2_eq {K : Type} [Field K] [CharP K 2]
    (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    frameLangSL2 ζ hζ = uSL (ζ ^ 2) * vSL (1 : K) := by
  have hsq := su6Cut_zeta_sq h2 hζ
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameLangSL2, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, hsq]
  all_goals linear_combination -h2

private def su6CutToSL {K : Type} [Field K] [Finite K] [CharP K 2] :
    CFSG.ClassicalInvolution.Phan.Su K 2 3 6 →* SL(6, K) where
  toFun X := ⟨((X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K), X.2.1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem su6BlkR_blockMat_one {K : Type} [Field K] (t : Fin 5) :
    CFSG.ClassicalInvolution.Phan.blockMat 6 t.val
      ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_one, CFSG.ClassicalInvolution.Phan.blockMat_one]

private theorem su6BlkR_blockMat_mul {K : Type} [Field K] (t : Fin 5) (Z W : SL(2, K)) :
    CFSG.ClassicalInvolution.Phan.blockMat 6 t.val
        ((Z * W : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      CFSG.ClassicalInvolution.Phan.blockMat 6 t.val (Z : Matrix (Fin 2) (Fin 2) K) *
        CFSG.ClassicalInvolution.Phan.blockMat 6 t.val (W : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul,
    CFSG.ClassicalInvolution.Phan.blockMat_mul (m := 6) (i := t.val) (by omega)]

private noncomputable def su6BlkR_block {K : Type} [Field K] (t : Fin 5) :
    SL(2, K) →* SL(6, K) where
  toFun Z := ⟨CFSG.ClassicalInvolution.Phan.blockMat 6 t.val
      (Z : Matrix (Fin 2) (Fin 2) K), by
    rw [CFSG.ClassicalInvolution.Phan.det_blockMat (m := 6) (i := t.val) (by omega)]
    exact Z.2⟩
  map_one' := Subtype.ext (su6BlkR_blockMat_one t)
  map_mul' Z W := Subtype.ext (su6BlkR_blockMat_mul t Z W)

private theorem su6BlkR_sl2Upper_eq_uSL {K : Type} [Field K] (c : K) :
    CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c = uSL c :=
  Subtype.ext rfl

private theorem su6BlkR_sl2Lower_eq_vSL {K : Type} [Field K] (c : K) :
    CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c = vSL c :=
  Subtype.ext rfl

private theorem su6BlkR_blockMat_uSL {K : Type} [Field K] (t : Fin 5) (c : K) :
    CFSG.ClassicalInvolution.Phan.blockMat 6 t.val
        ((uSL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.transvection t.castSucc t.succ c := by
  ext r s
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases t <;> fin_cases r <;> fin_cases s <;>
    simp [uSL, Matrix.transvection, Matrix.add_apply, Fin.castSucc, Fin.succ]

private theorem su6BlkR_blockMat_vSL {K : Type} [Field K] (t : Fin 5) (c : K) :
    CFSG.ClassicalInvolution.Phan.blockMat 6 t.val
        ((vSL c : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.transvection t.succ t.castSucc c := by
  ext r s
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases t <;> fin_cases r <;> fin_cases s <;>
    simp [vSL, Matrix.transvection, Matrix.add_apply, Fin.castSucc, Fin.succ]

private theorem su6BlkR_block_uSL {K : Type} [Field K] (t : Fin 5) (c : K) :
    su6BlkR_block t (uSL c) =
      Matrix.SpecialLinearGroup.transvection
        (CFSG.LieType.Chevalley.E6GraphLevi.castSucc_ne_succ t) c := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  exact su6BlkR_blockMat_uSL t c

private theorem su6BlkR_block_vSL {K : Type} [Field K] (t : Fin 5) (c : K) :
    su6BlkR_block t (vSL c) =
      Matrix.SpecialLinearGroup.transvection
        (CFSG.LieType.Chevalley.E6GraphLevi.castSucc_ne_succ t).symm c := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.transvection_coe]
  exact su6BlkR_blockMat_vSL t c

private theorem su6BlkR_block_toSL {K : Type} [Field K] [Finite K] [CharP K 2] (t : Fin 5)
    (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2) :
    su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y) =
      su6BlkR_block t
        ⟨((Y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), Y.2.1⟩ := by
  refine Subtype.ext ?_
  exact CFSG.ClassicalInvolution.Phan.coe_coe_blockEmb (K := K) (p := 2) (f := 3)
    (m := 6) (k := 2) (i := t.val) (by omega) Y

private def su6Cutg {K : Type} [Field K] (ζ : K) : SL(6, K) :=
  CFSG.Timmesfeld.tv (2 : Fin 6) 3 (ζ ^ 2) * CFSG.Timmesfeld.tv (3 : Fin 6) 2 (1 : K) *
  CFSG.Timmesfeld.tv (1 : Fin 6) 4 (ζ ^ 2) * CFSG.Timmesfeld.tv (4 : Fin 6) 1 (1 : K) *
  CFSG.Timmesfeld.tv (0 : Fin 6) 5 (ζ ^ 2) * CFSG.Timmesfeld.tv (5 : Fin 6) 0 (1 : K)

private def su6CutgMat {K : Type} [Field K] (ζ : K) : Matrix (Fin 6) (Fin 6) K :=
  !![ζ, 0, 0, 0, 0, ζ ^ 2;
     0, ζ, 0, 0, ζ ^ 2, 0;
     0, 0, ζ, ζ ^ 2, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 1, 0, 0, 1, 0;
     1, 0, 0, 0, 0, 1]

private def su6CutQFun (x : Fin 2 × Fin 3) : Fin 6 :=
  if x.1 = 0 then ⟨x.2.val, by have := x.2.isLt; omega⟩ else
    ⟨5 - x.2.val, by have := x.2.isLt; omega⟩

private def su6CutQInv (i : Fin 6) : Fin 2 × Fin 3 :=
  if h : i.val < 3 then (0, ⟨i.val, by omega⟩) else
    (1, ⟨5 - i.val, by have := i.isLt; omega⟩)

private def su6CutQEquiv : (Fin 2 × Fin 3) ≃ Fin 6 where
  toFun := su6CutQFun
  invFun := su6CutQInv
  left_inv := by rintro ⟨s, p⟩; fin_cases s <;> fin_cases p <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def su6CutQ : (Fin 2 × Fin 3) ≃ Fin 6 := su6CutQEquiv

private theorem su6CutgMat_eq_reindex {K : Type} [Field K] {ζ : K} :
    su6CutgMat ζ = Matrix.reindexAlgEquiv K K su6CutQ
      (Matrix.blockDiagonal (fun _ : Fin 3 => su6CutA ζ)) := by
  rw [Matrix.coe_reindexAlgEquiv]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [su6CutgMat, su6CutA, su6CutQ, su6CutQEquiv, su6CutQInv,
      Matrix.reindex_apply, Matrix.blockDiagonal_apply]

private def su6CutPairBlock {K : Type} [Field K] (p : Fin 3) (ζ : K) : SL(6, K) :=
  match p.val with
  | 0 => CFSG.Timmesfeld.tv (0 : Fin 6) 5 (ζ ^ 2) * CFSG.Timmesfeld.tv 5 0 (1 : K)
  | 1 => CFSG.Timmesfeld.tv (1 : Fin 6) 4 (ζ ^ 2) * CFSG.Timmesfeld.tv 4 1 (1 : K)
  | _ => CFSG.Timmesfeld.tv (2 : Fin 6) 3 (ζ ^ 2) * CFSG.Timmesfeld.tv 3 2 (1 : K)

private theorem su6CutN_transpose {K : Type} [Field K] :
    (su6CutN (K := K)).transpose = su6CutN := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su6CutN]

private theorem su6CutN_mul_self {K : Type} [Field K] :
    su6CutN (K := K) * su6CutN = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su6CutN, Matrix.mul_apply, Fin.sum_univ_two]

private theorem su6Cut_antiId_eq_reindex {K : Type} [Field K] :
    CFSG.LieType.Chevalley.E6GraphLevi.antiId K =
      Matrix.reindexAlgEquiv K K su6CutQ
        (Matrix.blockDiagonal (fun _ : Fin 3 => su6CutN (K := K))) := by
  change CFSG.LieType.Chevalley.E6GraphLevi.antiId K =
    Matrix.reindex su6CutQ su6CutQ
      (Matrix.blockDiagonal (fun _ : Fin 3 => su6CutN (K := K)))
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [CFSG.LieType.Chevalley.E6GraphLevi.antiId, su6CutN, su6CutQ, su6CutQEquiv,
      su6CutQInv, Matrix.reindex_apply, Matrix.blockDiagonal_apply]

private theorem su6Cut_reindex_map {K : Type} [Field K] {σ : K ≃+* K}
    (M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) :
    (Matrix.reindexAlgEquiv K K su6CutQ M).map σ.toRingHom =
      Matrix.reindexAlgEquiv K K su6CutQ (M.map σ.toRingHom) := by
  change (Matrix.reindex su6CutQ su6CutQ M).map σ.toRingHom =
    Matrix.reindex su6CutQ su6CutQ (M.map σ.toRingHom)
  ext i j
  simp [Matrix.reindex_apply, Matrix.map_apply]

private theorem su6Cut_reindex_transpose {K : Type} [Field K]
    (M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K) :
    (Matrix.reindexAlgEquiv K K su6CutQ M).transpose =
      Matrix.reindexAlgEquiv K K su6CutQ M.transpose := by
  change (Matrix.reindex su6CutQ su6CutQ M).transpose =
    Matrix.reindex su6CutQ su6CutQ M.transpose
  ext i j
  simp [Matrix.reindex_apply, Matrix.transpose_apply]

private theorem su6Cut_sigmaAtNA {K : Type} [Field K] {σ : K ≃+* K} {ζ : K}
    (h2 : (2 : K) = 0) (hζ : ζ ^ 2 + ζ + 1 = 0) (hσζ : σ ζ = ζ ^ 2)
    (hζ4 : ζ ^ 4 = ζ) :
    ((su6CutA ζ).map σ.toRingHom).transpose * su6CutN * su6CutA ζ = 1 := by
  rw [su6Cut_A_sigma hσζ hζ4, Matrix.transpose_mul, su6CutN_transpose]
  calc su6CutN * (su6CutA ζ).transpose * su6CutN * su6CutA ζ
      = su6CutN * (((su6CutA ζ).transpose * su6CutN) * su6CutA ζ) := by
        noncomm_ring
    _ = su6CutN * su6CutN := by rw [su6Cut_AtNA h2 hζ]
    _ = 1 := su6CutN_mul_self

private theorem su6Cut_block_form {K : Type} [Field K] {σ : K ≃+* K} {ζ : K}
    (h2 : (2 : K) = 0) (hζ : ζ ^ 2 + ζ + 1 = 0) (hσζ : σ ζ = ζ ^ 2)
    (hζ4 : ζ ^ 4 = ζ) :
    ((Matrix.blockDiagonal (fun _ : Fin 3 => su6CutA ζ)).map σ.toRingHom).transpose *
        Matrix.blockDiagonal (fun _ : Fin 3 => su6CutN) *
        Matrix.blockDiagonal (fun _ : Fin 3 => su6CutA ζ) = 1 := by
  have hmap : (Matrix.blockDiagonal (fun _ : Fin 3 => su6CutA ζ)).map σ.toRingHom =
      Matrix.blockDiagonal (fun _ : Fin 3 => (su6CutA ζ).map σ.toRingHom) := by
    ext i j
    by_cases h : i.2 = j.2 <;> simp [Matrix.blockDiagonal_apply, Matrix.map_apply, h]
  have htr : (Matrix.blockDiagonal (fun _ : Fin 3 => (su6CutA ζ).map σ.toRingHom)).transpose =
      Matrix.blockDiagonal (fun _ : Fin 3 => ((su6CutA ζ).map σ.toRingHom).transpose) := by
    ext i j
    by_cases h : i.2 = j.2 <;> simp [Matrix.blockDiagonal_apply, Matrix.transpose_apply, h, eq_comm]
  rw [hmap, htr, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  rw [show (fun _ : Fin 3 =>
        ((su6CutA ζ).map σ.toRingHom).transpose * su6CutN * su6CutA ζ) =
      (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) K)) by
    funext q
    exact su6Cut_sigmaAtNA h2 hζ hσζ hζ4]
  rw [show Matrix.blockDiagonal (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 by
    ext i j
    rcases i with ⟨i1, i2⟩
    rcases j with ⟨j1, j2⟩
    by_cases h1 : i1 = j1 <;> by_cases h2 : i2 = j2 <;>
      simp [Matrix.blockDiagonal_apply, Matrix.one_apply, h1, h2]]

private theorem su6Cut_g_form {K : Type} [Field K] {σ : K ≃+* K} {ζ : K}
    (h2 : (2 : K) = 0) (hζ : ζ ^ 2 + ζ + 1 = 0) (hσζ : σ ζ = ζ ^ 2)
    (hζ4 : ζ ^ 4 = ζ) :
    ((su6CutgMat ζ).map σ.toRingHom).transpose *
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K * su6CutgMat ζ = 1 := by
  rw [su6CutgMat_eq_reindex, su6Cut_antiId_eq_reindex]
  rw [su6Cut_reindex_map, su6Cut_reindex_transpose]
  rw [← map_mul, ← map_mul]
  rw [su6Cut_block_form h2 hζ hσζ hζ4, map_one]

private def su6CutTransposeGL {K : Type} [Field K] (G : GL (Fin 6) K) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((G : Matrix (Fin 6) (Fin 6) K).transpose)
    (by
      rw [Matrix.det_transpose]
      exact G.det_ne_zero)

private theorem su6CutTransposeGL_coe {K : Type} [Field K] (G : GL (Fin 6) K) :
    (su6CutTransposeGL G : Matrix (Fin 6) (Fin 6) K) =
      (G : Matrix (Fin 6) (Fin 6) K).transpose :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem su6CutTransposeGL_one {K : Type} [Field K] :
    su6CutTransposeGL (1 : GL (Fin 6) K) = 1 := by
  apply Units.ext
  ext i j
  simp [su6CutTransposeGL_coe, Matrix.one_apply, eq_comm]

private theorem su6CutTransposeGL_mul {K : Type} [Field K] (G H : GL (Fin 6) K) :
    su6CutTransposeGL (G * H) = su6CutTransposeGL H * su6CutTransposeGL G := by
  apply Units.ext
  ext i j
  simp only [su6CutTransposeGL_coe, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem su6CutTransposeGL_inv {K : Type} [Field K] (G : GL (Fin 6) K) :
    su6CutTransposeGL G⁻¹ = (su6CutTransposeGL G)⁻¹ := by
  have h : su6CutTransposeGL G * su6CutTransposeGL G⁻¹ = 1 := by
    rw [← su6CutTransposeGL_mul, inv_mul_cancel, su6CutTransposeGL_one]
  exact eq_inv_of_mul_eq_one_right h

private def su6CutJGL {K : Type} [Field K] : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (CFSG.LieType.Chevalley.E6GraphLevi.antiId K)
    (by
      intro h
      have hh := congrArg Matrix.det
        (CFSG.LieType.Chevalley.E6GraphLevi.antiId_mul_self (E := K))
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hh
      exact zero_ne_one hh)

private theorem su6CutJGL_coe {K : Type} [Field K] :
    (su6CutJGL (K := K) : Matrix (Fin 6) (Fin 6) K) =
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem su6CutJGL_mul_self {K : Type} [Field K] :
    su6CutJGL (K := K) * su6CutJGL = 1 := by
  apply Units.ext
  change CFSG.LieType.Chevalley.E6GraphLevi.antiId K *
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K =
    (1 : Matrix (Fin 6) (Fin 6) K)
  rw [CFSG.LieType.Chevalley.E6GraphLevi.antiId_mul_self]

private theorem su6Cut_inv_form {K : Type} [Field K] {σ : K ≃+* K} (G : GL (Fin 6) K)
    (hform : ((G : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose *
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K *
      (G : Matrix (Fin 6) (Fin 6) K) = 1) :
    (((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose *
      ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        CFSG.LieType.Chevalley.E6GraphLevi.antiId K := by
  let Gσ : GL (Fin 6) K := Matrix.GeneralLinearGroup.map σ.toRingHom G
  have hGσ : (Gσ : Matrix (Fin 6) (Fin 6) K) =
      (G : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom := rfl
  have hformGL : su6CutTransposeGL Gσ * su6CutJGL (K := K) * G = 1 := by
    apply Units.ext
    change (Gσ : Matrix (Fin 6) (Fin 6) K).transpose *
        CFSG.LieType.Chevalley.E6GraphLevi.antiId K *
        (G : Matrix (Fin 6) (Fin 6) K) = 1
    rw [hGσ]
    exact hform
  have h1 : su6CutTransposeGL Gσ * su6CutJGL (K := K) = G⁻¹ := by
    have h := congrArg (fun x : GL (Fin 6) K => x * G⁻¹) hformGL
    simpa [mul_assoc] using h
  have h2 : su6CutTransposeGL Gσ = G⁻¹ * su6CutJGL (K := K) := by
    calc su6CutTransposeGL Gσ =
          su6CutTransposeGL Gσ * (su6CutJGL (K := K) * su6CutJGL (K := K)) := by
          rw [su6CutJGL_mul_self (K := K), mul_one]
      _ = (su6CutTransposeGL Gσ * su6CutJGL (K := K)) * su6CutJGL (K := K) := by rw [mul_assoc]
      _ = G⁻¹ * su6CutJGL (K := K) := by rw [h1]
  have hJinv : (su6CutJGL (K := K))⁻¹ = su6CutJGL (K := K) := by
    calc (su6CutJGL (K := K))⁻¹ =
          (su6CutJGL (K := K))⁻¹ * (su6CutJGL (K := K) * su6CutJGL (K := K)) := by
          rw [su6CutJGL_mul_self (K := K), mul_one]
      _ = ((su6CutJGL (K := K))⁻¹ * su6CutJGL (K := K)) * su6CutJGL (K := K) := by rw [mul_assoc]
      _ = 1 * su6CutJGL (K := K) := by rw [inv_mul_cancel]
      _ = su6CutJGL (K := K) := by rw [one_mul]
  have h3 : (su6CutTransposeGL Gσ)⁻¹ * G⁻¹ = su6CutJGL (K := K) := by
    rw [h2, mul_inv_rev, hJinv, inv_inv]
    group
  have hPσ : Matrix.GeneralLinearGroup.map σ.toRingHom G⁻¹ = Gσ⁻¹ :=
    map_inv (Matrix.GeneralLinearGroup.map σ.toRingHom) G
  change (((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose *
      ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        CFSG.LieType.Chevalley.E6GraphLevi.antiId K
  have hcoe : ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom =
      ((Matrix.GeneralLinearGroup.map σ.toRingHom G⁻¹ : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) := rfl
  rw [hcoe, ← su6CutTransposeGL_coe (Matrix.GeneralLinearGroup.map σ.toRingHom G⁻¹),
    hPσ, su6CutTransposeGL_inv, ← Matrix.GeneralLinearGroup.coe_mul, h3,
    su6CutJGL_coe (K := K)]

private theorem su6CutPairBlock_coe {K : Type} [Field K] [CharP K 2] (p : Fin 3)
    (h2 : (2 : K) = 0) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ((su6CutPairBlock p ζ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.reindexAlgEquiv K K su6CutQ
        (Matrix.blockDiagonal (fun q : Fin 3 => if q = p then su6CutA ζ else 1)) := by
  have hsq := su6Cut_zeta_sq h2 hζ
  fin_cases p <;>
    simp only [su6CutPairBlock] <;>
    rw [CFSG.Timmesfeld.tv_of_ne (by decide), CFSG.Timmesfeld.tv_of_ne (by decide),
      Matrix.SpecialLinearGroup.coe_mul, Matrix.coe_reindexAlgEquiv] <;>
    ext r s <;>
    fin_cases r <;> fin_cases s <;>
    simp [su6CutQ, su6CutQEquiv, su6CutQInv, su6CutA, Matrix.reindex_apply,
      Matrix.blockDiagonal_apply, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, hsq] <;>
    linear_combination h2

private theorem su6Cutg_coe {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    ((su6Cutg ζ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = su6CutgMat ζ := by
  have hgroup : su6Cutg ζ =
      su6CutPairBlock 2 ζ * su6CutPairBlock 1 ζ * su6CutPairBlock 0 ζ := by
    simp [su6Cutg, su6CutPairBlock]
    group
  rw [hgroup, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    su6CutPairBlock_coe 2 h2 hζ, su6CutPairBlock_coe 1 h2 hζ,
    su6CutPairBlock_coe 0 h2 hζ, su6CutgMat_eq_reindex]
  rw [← map_mul, ← map_mul]
  have hR : (Matrix.blockDiagonal (fun q : Fin 3 => if q = 2 then su6CutA ζ else 1) *
        Matrix.blockDiagonal (fun q : Fin 3 => if q = 1 then su6CutA ζ else 1)) *
        Matrix.blockDiagonal (fun q : Fin 3 => if q = 0 then su6CutA ζ else 1) =
      Matrix.blockDiagonal (fun _ : Fin 3 => su6CutA ζ) := by
    rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
    congr 1
    funext q
    fin_cases q <;> simp
  exact congrArg (Matrix.reindexAlgEquiv K K su6CutQ) hR

private def su6GenA_star {K : Type} [Field K] (σ : K ≃+* K) (A : GL (Fin 6) K) :
    GL (Fin 6) K :=
  su6CutTransposeGL (Matrix.GeneralLinearGroup.map σ.toRingHom A)

private theorem su6GenA_star_coe {K : Type} [Field K] (σ : K ≃+* K) (A : GL (Fin 6) K) :
    ((su6GenA_star σ A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((A : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose := by
  rw [su6GenA_star, su6CutTransposeGL_coe]
  rfl

private theorem su6GenA_star_mul {K : Type} [Field K] (σ : K ≃+* K) (A B : GL (Fin 6) K) :
    su6GenA_star σ (A * B) = su6GenA_star σ B * su6GenA_star σ A := by
  simp only [su6GenA_star, map_mul, su6CutTransposeGL_mul]

private theorem su6GenA_star_conj_inv {K : Type} [Field K] (σ : K ≃+* K)
    (G B : GL (Fin 6) K)
    (hG : su6GenA_star σ G * su6CutJGL * G = 1)
    (hGinv : su6GenA_star σ G⁻¹ * G⁻¹ = su6CutJGL)
    (hB : su6GenA_star σ B * su6CutJGL * B = su6CutJGL) :
    su6GenA_star σ (G⁻¹ * B * G) * (G⁻¹ * B * G) = 1 := by
  calc su6GenA_star σ (G⁻¹ * B * G) * (G⁻¹ * B * G)
      = (su6GenA_star σ G * su6GenA_star σ B * su6GenA_star σ G⁻¹) *
          (G⁻¹ * B * G) := by
        rw [su6GenA_star_mul, su6GenA_star_mul]
        group
    _ = su6GenA_star σ G * su6GenA_star σ B * (su6GenA_star σ G⁻¹ * G⁻¹) * B * G := by
        group
    _ = su6GenA_star σ G * su6GenA_star σ B * su6CutJGL * B * G := by rw [hGinv]
    _ = su6GenA_star σ G * (su6GenA_star σ B * su6CutJGL * B) * G := by group
    _ = su6GenA_star σ G * su6CutJGL * G := by rw [hB]
    _ = 1 := hG

private theorem su6GenA_star_conj {K : Type} [Field K] (σ : K ≃+* K) (G X : GL (Fin 6) K)
    (hG : su6GenA_star σ G * su6CutJGL * G = 1)
    (hGinv : su6GenA_star σ G⁻¹ * G⁻¹ = su6CutJGL)
    (hX : su6GenA_star σ X * X = 1) :
    su6GenA_star σ (G * X * G⁻¹) * su6CutJGL * (G * X * G⁻¹) = su6CutJGL := by
  calc su6GenA_star σ (G * X * G⁻¹) * su6CutJGL * (G * X * G⁻¹)
      = (su6GenA_star σ G⁻¹ * su6GenA_star σ X * su6GenA_star σ G) *
          su6CutJGL * (G * X * G⁻¹) := by
        rw [su6GenA_star_mul, su6GenA_star_mul]
        group
    _ = su6GenA_star σ G⁻¹ * su6GenA_star σ X * (su6GenA_star σ G * su6CutJGL * G) *
          X * G⁻¹ := by group
    _ = su6GenA_star σ G⁻¹ * su6GenA_star σ X * X * G⁻¹ := by rw [hG]; group
    _ = su6GenA_star σ G⁻¹ * (su6GenA_star σ X * X) * G⁻¹ := by group
    _ = su6GenA_star σ G⁻¹ * G⁻¹ := by rw [hX]; simp
    _ = su6CutJGL := hGinv

private theorem su6Cut_unitarySL_eq {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    CFSG.LieType.Chevalley.E6GraphLevi.unitarySL σ.toRingHom =
      (⊤ : Subgroup (CFSG.ClassicalInvolution.Phan.Su K 2 3 6)).map
        ((MulAut.conj (su6Cutg ζ)).toMonoidHom.comp su6CutToSL) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσζ : σ ζ = ζ ^ 2 := su6Cut_sigma_zeta h2 hσ hζ
  have hζ4 : ζ ^ 4 = ζ := su6Cut_zeta_pow_four h2 hζ
  have hconjTr : ∀ M : Matrix (Fin 6) (Fin 6) K,
      CFSG.LieType.Universal.Unitary.conjTr
          (CFSG.LieType.BorelTits.unitaryInvolution K 2 3) M =
        (M.map σ.toRingHom).transpose := by
    intro M
    rw [CFSG.LieType.Universal.Unitary.conjTr]
    congr 1
    ext i j
    simp only [Matrix.map_apply]
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
    show M i j ^ 2 ^ 3 = σ (M i j)
    rw [hσ]
    norm_num
  let G : GL (Fin 6) K := Matrix.SpecialLinearGroup.toGL (su6Cutg ζ)
  have hGm : (G : Matrix (Fin 6) (Fin 6) K) = su6CutgMat ζ := by
    dsimp only [G]
    exact su6Cutg_coe h2 hζ
  have hGdet : Matrix.GeneralLinearGroup.det G = 1 := by
    dsimp only [G]
    exact Matrix.SpecialLinearGroup.coeToGL_det (su6Cutg ζ)
  have hGform : ((G : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose *
      CFSG.LieType.Chevalley.E6GraphLevi.antiId K * (G : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [hGm]
    exact su6Cut_g_form h2 hζ hσζ hζ4
  have hGstar : su6GenA_star σ G * su6CutJGL * G = 1 := by
    apply Units.ext
    change ((su6GenA_star σ G : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((su6CutJGL : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (G : Matrix (Fin 6) (Fin 6) K) =
      (1 : Matrix (Fin 6) (Fin 6) K)
    rw [su6GenA_star_coe, su6CutJGL_coe, hGform]
  have hinv : (((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose *
      ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        CFSG.LieType.Chevalley.E6GraphLevi.antiId K :=
    su6Cut_inv_form G hGform
  have hGinvstar : su6GenA_star σ G⁻¹ * G⁻¹ = su6CutJGL := by
    apply Units.ext
    change ((su6GenA_star σ G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((G⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      ((su6CutJGL : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    rw [su6GenA_star_coe, su6CutJGL_coe]
    exact hinv
  apply le_antisymm
  · intro B hB
    rw [Subgroup.mem_map]
    have hBmat : ((B : Matrix (Fin 6) (Fin 6) K).map σ.toRingHom).transpose *
        CFSG.LieType.Chevalley.E6GraphLevi.antiId K *
        (B : Matrix (Fin 6) (Fin 6) K) = CFSG.LieType.Chevalley.E6GraphLevi.antiId K :=
      (CFSG.LieType.Chevalley.E6GraphLevi.mem_unitarySL_iff).mp hB
    let Bgl : GL (Fin 6) K := Matrix.SpecialLinearGroup.toGL B
    have hBdet : Matrix.GeneralLinearGroup.det Bgl = 1 := by
      dsimp only [Bgl]
      exact Matrix.SpecialLinearGroup.coeToGL_det B
    have hBstar : su6GenA_star σ Bgl * su6CutJGL * Bgl = su6CutJGL := by
      apply Units.ext
      change ((su6GenA_star σ Bgl : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((su6CutJGL : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * (Bgl : Matrix (Fin 6) (Fin 6) K) =
        ((su6CutJGL : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
      rw [su6GenA_star_coe, su6CutJGL_coe]
      dsimp only [Bgl]
      exact hBmat
    let X : GL (Fin 6) K := G⁻¹ * Bgl * G
    have hXstar : su6GenA_star σ X * X = 1 := by
      dsimp only [X]
      exact su6GenA_star_conj_inv σ G Bgl hGstar hGinvstar hBstar
    have hXdet : (X : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      have hdet : Matrix.GeneralLinearGroup.det X = 1 := by
        dsimp only [X]
        rw [map_mul, map_mul, map_inv, hGdet, hBdet]
        simp
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
    have hXform : CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 3)
        (X : Matrix (Fin 6) (Fin 6) K) * (X : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [hconjTr, ← su6GenA_star_coe]
      simpa using congrArg (fun A : GL (Fin 6) K =>
        (A : Matrix (Fin 6) (Fin 6) K)) hXstar
    have hXmem : X ∈ CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 3) 6 :=
      ⟨hXdet, hXform⟩
    refine ⟨⟨X, hXmem⟩, Subgroup.mem_top _, ?_⟩
    show (MulAut.conj (su6Cutg ζ)) (su6CutToSL ⟨X, hXmem⟩) = B
    rw [MulAut.conj_apply]
    apply Matrix.SpecialLinearGroup.toGL_injective
    have htoGLX : Matrix.SpecialLinearGroup.toGL (su6CutToSL ⟨X, hXmem⟩) = X := by
      apply Units.ext
      ext i j
      rfl
    rw [map_mul, map_mul, map_inv, htoGLX]
    change G * X * G⁻¹ = Matrix.SpecialLinearGroup.toGL B
    rw [show X = G⁻¹ * Bgl * G from rfl]
    dsimp only [Bgl]
    group
  · intro B hB
    rw [Subgroup.mem_map] at hB
    obtain ⟨Xsu, -, hXeq⟩ := hB
    rw [← hXeq]
    change su6Cutg ζ * su6CutToSL Xsu * (su6Cutg ζ)⁻¹ ∈
      CFSG.LieType.Chevalley.E6GraphLevi.unitarySL σ.toRingHom
    rw [CFSG.LieType.Chevalley.E6GraphLevi.mem_unitarySL_iff]
    let X : GL (Fin 6) K := Matrix.SpecialLinearGroup.toGL (su6CutToSL Xsu)
    have hXmem : X ∈ CFSG.LieType.Universal.Unitary.SUid
        (CFSG.LieType.BorelTits.unitaryInvolution K 2 3) 6 := by
      dsimp only [X]
      exact Xsu.2
    have hXstar : su6GenA_star σ X * X = 1 := by
      apply Units.ext
      change ((su6GenA_star σ X : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (X : Matrix (Fin 6) (Fin 6) K) = (1 : Matrix (Fin 6) (Fin 6) K)
      rw [su6GenA_star_coe]
      have h := hXmem.2
      rw [hconjTr] at h
      exact h
    let Bgl : GL (Fin 6) K := Matrix.SpecialLinearGroup.toGL
      (su6Cutg ζ * su6CutToSL Xsu * (su6Cutg ζ)⁻¹)
    have hBgl : Bgl = G * X * G⁻¹ := by
      dsimp only [Bgl, X, G]
      rw [map_mul, map_mul, map_inv]
    have hBstar : su6GenA_star σ Bgl * su6CutJGL * Bgl = su6CutJGL := by
      rw [hBgl]
      exact su6GenA_star_conj σ G X hGstar hGinvstar hXstar
    have h := congrArg (fun A : GL (Fin 6) K =>
      (A : Matrix (Fin 6) (Fin 6) K)) hBstar
    have hB0 : (Bgl : Matrix (Fin 6) (Fin 6) K) =
        (↑(su6Cutg ζ * su6CutToSL Xsu * (su6Cutg ζ)⁻¹) :
          Matrix (Fin 6) (Fin 6) K) := by
      dsimp only [Bgl]
      rfl
    change ((su6GenA_star σ Bgl : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((su6CutJGL : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (Bgl : Matrix (Fin 6) (Fin 6) K) =
      ((su6CutJGL : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) at h
    rw [su6GenA_star_coe, su6CutJGL_coe, hB0] at h
    exact h

private theorem su6Cut_psi_eq_realize
    {K : Type} [Field K] (h2 : (2 : K) = 0)
    {σ : K ≃+* K} {Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K}
    (hΨ : TwSU6.IsPsiTw σ.toRingHom (1 : K) Ψ) :
    Ψ = CFSG.LieType.Chevalley.E6GraphLevi.realize h2 := by
  apply MonoidHom.eq_of_eqOn_dense
    (CFSG.LieType.Chevalley.E6GraphLevi.closure_adjacentSet (E := K))
  rintro g ⟨t, c, rfl | rfl⟩
  · have hu : Ψ (Matrix.SpecialLinearGroup.transvection
          (CFSG.LieType.Chevalley.E6GraphLevi.castSucc_ne_succ t) c) =
        xUnit TwistTag.E6.tag K (TwSU6.a5Node t) c := by
      rw [← CFSG.Timmesfeld.tv_of_ne (CFSG.LieType.Chevalley.E6GraphLevi.castSucc_ne_succ t) c,
        hΨ.upper]
      congr 1
      rw [show TwSU6.eTw (1 : K) t = 1 from by
        fin_cases t <;>
          simp [TwSU6.eTw, CFSG.LieType.Chevalley.E6GraphLevi.neg_eq_self_of_two h2],
        one_mul]
    rw [hu, CFSG.LieType.Chevalley.E6GraphLevi.realize_x h2]
    rfl
  · have hv : Ψ (Matrix.SpecialLinearGroup.transvection
          (CFSG.LieType.Chevalley.E6GraphLevi.castSucc_ne_succ t).symm c) =
        yUnit TwistTag.E6.tag K (TwSU6.a5Node t) c := by
      rw [← CFSG.Timmesfeld.tv_of_ne
        (CFSG.LieType.Chevalley.E6GraphLevi.castSucc_ne_succ t).symm c, hΨ.lower]
      congr 1
      rw [show TwSU6.eTw (1 : K) t = 1 from by
        fin_cases t <;>
          simp [TwSU6.eTw, CFSG.LieType.Chevalley.E6GraphLevi.neg_eq_self_of_two h2]]
      simp
    rw [hv, CFSG.LieType.Chevalley.E6GraphLevi.realize_y h2]
    rfl

section Certificates

variable {K : Type} [Field K] [CharP K 2]

private theorem su6Cut_rootSL2_frameLangSL2 {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0)
    {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) :
    rootSL2 TwistTag.E6.tag K β (frameLangSL2 ζ hζ) =
      pinnedX TwistTag.E6.tag K β (ζ ^ 2) * pinnedX TwistTag.E6.tag K (-β) 1 := by
  rw [su6Cut_frameLangSL2_eq h2 hζ]
  simp only [map_mul, rootSL2_uSL_eq]
  have hsign : (pinnedData TwistTag.E6.tag β).2.2 • (ζ ^ 2) = ζ ^ 2 := by
    rcases CFSG.Blueprint.Chevalley.pinnedSign_eq TwistTag.E6.tag β with h | h <;> rw [h] <;>
      simp [CFSG.LieType.Chevalley.E6GraphLevi.neg_eq_self_of_two h2]
  rw [hsign]
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := K) hβ
  rw [hv]
  have hε1 : ε = 1 := eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε
  rw [hε1, one_mul]

private theorem su6Cut_realize_pair {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) {i j : Fin 6} (hij : i ≠ j)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβeq : β = CFSG.LieType.Chevalley.E6GraphLevi.matRoot i j)
    (hβ : IsRoot TwistTag.E6.tag β) :
    CFSG.LieType.Chevalley.E6GraphLevi.realize h2
        (CFSG.Timmesfeld.tv i j (ζ ^ 2) * CFSG.Timmesfeld.tv j i (1 : K)) =
      rootSL2 TwistTag.E6.tag K β (frameLangSL2 ζ hζ) := by
  rw [CFSG.Timmesfeld.tv_of_ne hij, CFSG.Timmesfeld.tv_of_ne hij.symm, map_mul,
    CFSG.SeitzReduction.TwistedE6Pilot.realize_transvection_ovl h2 hij (ζ ^ 2),
    CFSG.SeitzReduction.TwistedE6Pilot.realize_transvection_ovl h2 hij.symm 1,
    show CFSG.LieType.Chevalley.E6GraphLevi.matRoot j i =
      -CFSG.LieType.Chevalley.E6GraphLevi.matRoot i j from
        CFSG.SeitzReduction.TwistedE6Pilot.matRoot_swap_ovl i j,
    su6Cut_rootSL2_frameLangSL2 h2 hζ hβ, hβeq]

private theorem su6Cut_rootSL2_uSL_eq {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (c : K) :
    rootSL2 TwistTag.E6.tag K β (uSL c) =
      pinnedX TwistTag.E6.tag K β c := by
  rw [CFSG.LieType.Chevalley.rootSL2_uSL_eq]
  rcases CFSG.Blueprint.Chevalley.pinnedSign_eq TwistTag.E6.tag β with h | h <;>
    simp [h, CFSG.LieType.Chevalley.E6GraphLevi.neg_eq_self_of_two h2]

private theorem su6Cut_rootSL2_vSL_eq {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (c : K) :
    rootSL2 TwistTag.E6.tag K β (vSL c) =
      pinnedX TwistTag.E6.tag K (-β) c := by
  obtain ⟨ε, hε, h⟩ := CFSG.LieType.Chevalley.exists_rootSL2_vSL_eq (K := K) hβ
  have hε1 : ε = 1 :=
    CFSG.LieType.Chevalley.eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε
  rw [h, hε1, one_mul]

private theorem su6Cut_realize_g {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    CFSG.LieType.Chevalley.E6GraphLevi.realize h2 (su6Cutg ζ) =
      rootSL2 TwistTag.E6.tag K (frameRoot 0) (frameLangSL2 ζ hζ) *
      rootSL2 TwistTag.E6.tag K (frameRoot 1) (frameLangSL2 ζ hζ) *
      rootSL2 TwistTag.E6.tag K (frameRoot 2) (frameLangSL2 ζ hζ) := by
  have h0 : frameRoot 0 = CFSG.LieType.Chevalley.E6GraphLevi.matRoot 2 3 := by decide
  have h1 : frameRoot 1 = CFSG.LieType.Chevalley.E6GraphLevi.matRoot 1 4 := by decide
  have h2' : frameRoot 2 = CFSG.LieType.Chevalley.E6GraphLevi.matRoot 0 5 := by decide
  have h0r : IsRoot TwistTag.E6.tag (frameRoot 0) := isRoot_frameRoot 0
  have h1r : IsRoot TwistTag.E6.tag (frameRoot 1) := isRoot_frameRoot 1
  have h2r : IsRoot TwistTag.E6.tag (frameRoot 2) := isRoot_frameRoot 2
  have hgroup : su6Cutg ζ =
      (CFSG.Timmesfeld.tv (2 : Fin 6) 3 (ζ ^ 2) * CFSG.Timmesfeld.tv (3 : Fin 6) 2 (1 : K)) *
      (CFSG.Timmesfeld.tv (1 : Fin 6) 4 (ζ ^ 2) * CFSG.Timmesfeld.tv (4 : Fin 6) 1 (1 : K)) *
      (CFSG.Timmesfeld.tv (0 : Fin 6) 5 (ζ ^ 2) * CFSG.Timmesfeld.tv (5 : Fin 6) 0 (1 : K)) := by
    simp only [su6Cutg]
    group
  rw [hgroup]
  simp only [map_mul]
  rw [← map_mul, su6Cut_realize_pair h2 hζ (show (2 : Fin 6) ≠ 3 by decide) h0 h0r,
    ← map_mul, su6Cut_realize_pair h2 hζ (show (1 : Fin 6) ≠ 4 by decide) h1 h1r,
    ← map_mul, su6Cut_realize_pair h2 hζ (show (0 : Fin 6) ≠ 5 by decide) h2' h2r]

private theorem su6Cut_frameLang_eq {K : Type} [Field K] [CharP K 2] (h2 : (2 : K) = 0) {ζ : K}
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    frameLang ζ hζ = CFSG.LieType.Chevalley.E6GraphLevi.realize h2 (su6Cutg ζ) *
      rootSL2 TwistTag.E6.tag K e6HighestRoot (frameLangSL2 ζ hζ) := by
  rw [frameLang, su6Cut_realize_g h2 hζ]
  rfl

private theorem su6Cut_realize_block {K : Type} [Field K] [Finite K] [CharP K 2]
    (h2 : (2 : K) = 0) (t : Fin 5) (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2) :
    CFSG.LieType.Chevalley.E6GraphLevi.realize h2
        (su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)) =
      rootSL2 TwistTag.E6.tag K (Pi.single (CFSG.LieType.Chevalley.E6GraphLevi.pathIdx t) 1)
        ⟨((Y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), Y.2.1⟩ := by
  have hFG : (CFSG.LieType.Chevalley.E6GraphLevi.realize h2).comp (su6BlkR_block t) =
      rootSL2 TwistTag.E6.tag K
        (Pi.single (CFSG.LieType.Chevalley.E6GraphLevi.pathIdx t) 1) := by
    apply MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K))
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [su6BlkR_sl2Upper_eq_uSL, MonoidHom.comp_apply, su6BlkR_block_uSL,
        CFSG.LieType.Chevalley.E6GraphLevi.realize_x h2, su6Cut_rootSL2_uSL_eq h2,
        CFSG.Blueprint.Chevalley.pinnedX_single]
    · rw [su6BlkR_sl2Lower_eq_vSL, MonoidHom.comp_apply, su6BlkR_block_vSL,
        CFSG.LieType.Chevalley.E6GraphLevi.realize_y h2,
        su6Cut_rootSL2_vSL_eq h2 (isRoot_single TwistTag.E6.tag
          (CFSG.LieType.Chevalley.E6GraphLevi.pathIdx t)),
        CFSG.Blueprint.Chevalley.pinnedX_neg_single]
  rw [su6BlkR_block_toSL t Y]
  exact DFunLike.congr_fun hFG _

private theorem su6BlkM_comm {K : Type} [Field K] [Finite K] [CharP K 2]
    (h2 : (2 : K) = 0) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (t : Fin 5)
    (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2) :
    rootSL2 TwistTag.E6.tag K e6HighestRoot (frameLangSL2 ζ hζ) *
        CFSG.LieType.Chevalley.E6GraphLevi.realize h2
          (su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)) =
      CFSG.LieType.Chevalley.E6GraphLevi.realize h2
          (su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)) *
        rootSL2 TwistTag.E6.tag K e6HighestRoot (frameLangSL2 ζ hζ) := by
  have hXin : CFSG.LieType.Chevalley.E6GraphLevi.realize h2
      (su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)) ∈
      subsystemGroup TwistTag.E6.tag K CFSG.LieType.Chevalley.E6GraphLevi.setA := by
    rw [← CFSG.LieType.Chevalley.E6GraphLevi.range_realize h2]
    exact ⟨_, rfl⟩
  exact Subgroup.mem_centralizer_iff.1
    (CFSG.LieType.Chevalley.E6GraphLevi.subsystemGroup_le_centralizer_thetaSL2 h2 hXin)
    _ ⟨frameLangSL2 ζ hζ, rfl⟩

private theorem su6BlkM_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (h2 : (2 : K) = 0) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (t : Fin 5)
    (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2) :
    (baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ))⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          (CFSG.LieType.Chevalley.E6GraphLevi.realize h2
            (su6Cutg ζ * su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y) *
              (su6Cutg ζ)⁻¹)) *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (CFSG.LieType.Chevalley.E6GraphLevi.realize h2
          (su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y))) := by
  let g : SL(6, K) := su6Cutg ζ
  let X : SL(6, K) := su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)
  let T : ModGL TwistTag.E6.tag K :=
    rootSL2 TwistTag.E6.tag K e6HighestRoot (frameLangSL2 ζ hζ)
  let bc : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K))
  change (bc (frameLang ζ hζ))⁻¹ *
      bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 (g * X * g⁻¹)) *
      bc (frameLang ζ hζ) =
    bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X)
  have hcomm : T * CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X =
      CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X * T := su6BlkM_comm h2 hζ t Y
  have hcommbc : bc T * bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) =
      bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) * bc T := by
    calc bc T * bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X)
        = bc (T * CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) :=
          (map_mul bc T _).symm
      _ = bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X * T) := by rw [hcomm]
      _ = bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) * bc T := map_mul bc _ T
  have hT : (bc T)⁻¹ * bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) * bc T =
      bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) := by
    calc (bc T)⁻¹ * bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) * bc T
        = (bc T)⁻¹ *
            (bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) * bc T) := by group
      _ = (bc T)⁻¹ *
            (bc T * bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X)) := by
          rw [← hcommbc]
      _ = bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) := by group
  rw [su6Cut_frameLang_eq h2 hζ, map_mul]
  simp only [map_mul, map_inv]
  calc (bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 g) * bc T)⁻¹ *
        (bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 g) *
          bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) *
          (bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 g))⁻¹) *
        (bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 g) * bc T)
      = (bc T)⁻¹ * bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) * bc T := by
        group
    _ = bc (CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X) := hT

private theorem su6BlkM_mem_R {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hK : Nat.card K = 64) (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K} (hΨ : TwSU6.IsPsiTw σ.toRingHom 1 Ψ) (t : Fin 5)
    (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2) :
    Ψ (su6Cutg ζ * su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y) *
        (su6Cutg ζ)⁻¹) ∈ twistedE6RootGroup K σ := by
  let g : SL(6, K) := su6Cutg ζ
  let X : SL(6, K) := su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)
  change Ψ (g * X * g⁻¹) ∈ twistedE6RootGroup K σ
  have hconj : g * X * g⁻¹ ∈ CFSG.LieType.Chevalley.E6GraphLevi.unitarySL σ.toRingHom := by
    rw [su6Cut_unitarySL_eq hσ hζ, ← MulAut.conj_apply]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top X)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect
      (CFSG.LieType.Chevalley.E6GraphLevi.unitarySL σ.toRingHom) :=
    TwSU6.isPerfect_unitarySL_gen (p := 2) (f := 3) (K := K) (σ := σ.toRingHom)
      (by rw [hK]; norm_num)
      (by intro c; change σ c = c ^ 2 ^ 3; rw [hσ c]; norm_num)
  exact TwSU6.map_unitarySL_le_graphFixedRootGroup (K := K) (ε := 1) hΨ σ.surjective hperf
    ⟨g * X * g⁻¹, hconj, rfl⟩

private theorem su6BlkM_mem {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (h2 : (2 : K) = 0) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K} (hΨ : TwSU6.IsPsiTw σ.toRingHom 1 Ψ) (t : Fin 5)
    (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2)
    (hy : Ψ (su6Cutg ζ * su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y) *
        (su6Cutg ζ)⁻¹) ∈ twistedE6RootGroup K σ) :
    (⟨Ψ (su6Cutg ζ * su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y) *
        (su6Cutg ζ)⁻¹), hy⟩ : ↥(twistedE6RootGroup K σ)) ∈
      phiTwoCompIn (twistedE6RootGroup K σ)
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ))
        (Pi.single (CFSG.LieType.Chevalley.E6GraphLevi.pathIdx t) 1) := by
  let g : SL(6, K) := su6Cutg ζ
  let X : SL(6, K) := su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)
  let α : Fin TwistTag.E6.tag.rank → ℤ :=
    Pi.single (CFSG.LieType.Chevalley.E6GraphLevi.pathIdx t) 1
  let A : SL(2, K) :=
    ⟨((Y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), Y.2.1⟩
  let bc : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K))
  change (⟨Ψ (g * X * g⁻¹), hy⟩ : ↥(twistedE6RootGroup K σ)) ∈
    phiTwoCompIn (twistedE6RootGroup K σ) (bc (frameLang ζ hζ)) α
  rw [mem_phiTwoCompIn_iff]
  change (bc (frameLang ζ hζ))⁻¹ * bc (Ψ (g * X * g⁻¹)) * bc (frameLang ζ hζ) ∈
    rootSpan TwistTag.E6.tag (AlgebraicClosure K) {α, -α}
  rw [su6Cut_psi_eq_realize h2 hΨ, su6BlkM_conj h2 hζ t Y]
  rw [show CFSG.LieType.Chevalley.E6GraphLevi.realize h2 X =
      rootSL2 TwistTag.E6.tag K α A from su6Cut_realize_block h2 t Y]
  rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field
    (algebraMap K (AlgebraicClosure K)) α A]
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair
    (isRoot_single TwistTag.E6.tag _) _

private theorem su6Cut_block_mem {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hK : Nat.card K = 64) (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K} (hΨ : TwSU6.IsPsiTw σ.toRingHom 1 Ψ) (t : Fin 5)
    (Y : CFSG.ClassicalInvolution.Phan.Su K 2 3 2) :
    Ψ (su6Cutg ζ * su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y) *
        (su6Cutg ζ)⁻¹) ∈
      (PhiJoin K σ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ))).map
        (twistedE6RootGroup K σ).subtype := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let g : SL(6, K) := su6Cutg ζ
  let X : SL(6, K) := su6CutToSL (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t Y)
  let α : Fin TwistTag.E6.tag.rank → ℤ :=
    Pi.single (CFSG.LieType.Chevalley.E6GraphLevi.pathIdx t) 1
  let bc : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K))
  change Ψ (g * X * g⁻¹) ∈
    (PhiJoin K σ (bc (frameLang ζ hζ))).map (twistedE6RootGroup K σ).subtype
  have hy : Ψ (g * X * g⁻¹) ∈ twistedE6RootGroup K σ :=
    su6BlkM_mem_R hK hσ hζ hΨ t Y
  have hα : IsRoot TwistTag.E6.tag α := isRoot_single TwistTag.E6.tag _
  have hmem : (⟨Ψ (g * X * g⁻¹), hy⟩ : ↥(twistedE6RootGroup K σ)) ∈
      phiTwoCompIn (twistedE6RootGroup K σ) (bc (frameLang ζ hζ)) α :=
    su6BlkM_mem h2 hζ hΨ t Y hy
  have hjoin : (⟨Ψ (g * X * g⁻¹), hy⟩ : ↥(twistedE6RootGroup K σ)) ∈
      PhiJoin K σ (bc (frameLang ζ hζ)) := by
    change (⟨Ψ (g * X * g⁻¹), hy⟩ : ↥(twistedE6RootGroup K σ)) ∈
      ⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
        phiTwoCompIn (twistedE6RootGroup K σ) (bc (frameLang ζ hζ)) γ.1
    exact Subgroup.mem_iSup_of_mem
      (⟨α, hα⟩ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ}) hmem
  show (twistedE6RootGroup K σ).subtype ⟨Ψ (g * X * g⁻¹), hy⟩ ∈
    (PhiJoin K σ (bc (frameLang ζ hζ))).map (twistedE6RootGroup K σ).subtype
  exact Subgroup.mem_map_of_mem _ hjoin

end Certificates

theorem su6AmbientCut_frameLang
    {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hK : Nat.card K = 64) (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0)
    {Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K} (hΨ : TwSU6.IsPsiTw σ.toRingHom 1 Ψ) :
    SU6AmbientCut K σ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ)) Ψ := by
  rintro _ ⟨B, hB, rfl⟩
  rw [su6Cut_unitarySL_eq hσ hζ] at hB
  obtain ⟨X, -, rfl⟩ := hB
  have hX : X ∈ ⨆ t : Fin 5, (CFSG.ClassicalInvolution.Phan.blockEmb2 K 2 3 5 t).range := by
    rw [CFSG.ClassicalInvolution.Phan.iSup_range_blockEmb2 (p := 2) (f := 3)
      (hK.trans (by norm_num)) (by norm_num) 5]
    exact Subgroup.mem_top X
  refine Subgroup.iSup_induction _ (C := fun X =>
    Ψ (((MulAut.conj (su6Cutg ζ)).toMonoidHom.comp su6CutToSL) X) ∈
      (PhiJoin K σ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (frameLang ζ hζ))).map
        (twistedE6RootGroup K σ).subtype) hX ?_ ?_ ?_
  · rintro t _ ⟨Y, rfl⟩
    exact su6Cut_block_mem hK hσ hζ hΨ t Y
  · simp only [map_one]
    exact one_mem _
  · intro x y hx hy
    simp only [map_mul] at hx hy ⊢
    exact mul_mem hx hy

end CFSG.StandardType.PhiTwoRootGen

end
