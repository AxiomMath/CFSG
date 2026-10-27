module

public import CFSG.LocalAnalysis.StandardType.PhanEChevModel
public import CFSG.LocalAnalysis.StandardType.PhanEChevConj
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.Timmesfeld.RankTwo.SimplyLaced
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.TitsSimplicity
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT
  CFSG.Timmesfeld
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] (M : ChevModel2 D n H Fld)

@[expose] def a3Root (e : Fin 3 → Fin D.rank) (p q : Fin 4) : Fin D.rank → ℤ :=
  if p < q then ∑ k : Fin 3, if p.val ≤ k.val ∧ k.val < q.val then Pi.single (e k) 1 else 0
  else -∑ k : Fin 3, if q.val ≤ k.val ∧ k.val < p.val then Pi.single (e k) 1 else 0

@[expose] def IsA2Chart (θ : SL(3, Fld) →* K) (a b : Fin D.rank) : Prop :=
  ∀ c : Fld, θ (tv 0 1 c) = M.x (Pi.single a 1) c ∧ θ (tv 1 0 c) = M.x (-Pi.single a 1) c ∧
    θ (tv 1 2 c) = M.x (Pi.single b 1) c ∧ θ (tv 2 1 c) = M.x (-Pi.single b 1) c ∧
    θ (tv 0 2 c) = M.x (Pi.single a 1 + Pi.single b 1) c ∧
    θ (tv 2 0 c) = M.x (-(Pi.single a 1 + Pi.single b 1)) c

variable {M}

private theorem q2nPE_blk_zero : blk Fld 0 = blockSL Fld 3 2 0 (by omega) := rfl

private theorem q2nPE_blk_one : blk Fld 1 = blockSL Fld 3 2 1 (by omega) := rfl

theorem IsA2Chart.blk_middle {θ₀ θ₁ : SL(3, Fld) →* K} {a b c : Fin D.rank}
    (h₀ : IsA2Chart M θ₀ a b) (h₁ : IsA2Chart M θ₁ b c) :
    θ₀.comp (blk Fld 1) = θ₁.comp (blk Fld 0) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_tv_two (F := Fld)) ?_
  rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · show θ₀ (blk Fld 1 (tv 0 1 c)) = θ₁ (blk Fld 0 (tv 0 1 c))
    rw [blk_one_tv01, blk_zero_tv01, (h₀ c).2.2.1, (h₁ c).1]
  · show θ₀ (blk Fld 1 (tv 1 0 c)) = θ₁ (blk Fld 0 (tv 1 0 c))
    rw [blk_one_tv10, blk_zero_tv10, (h₀ c).2.2.2.1, (h₁ c).2.1]

theorem exists_a3_ctFamily {θ₀ θ₁ : SL(3, Fld) →* K} {a b c : Fin D.rank}
    (h₀ : IsA2Chart M θ₀ a b) (h₁ : IsA2Chart M θ₁ b c)
    (hcomm : ∀ A B : SL(2, Fld), Commute (θ₀ (blk Fld 0 A)) (θ₁ (blk Fld 1 B))) :
    ∃ F : CTFamily Fld K 3, F.θ 0 = θ₀ ∧ F.θ 1 = θ₁ := by
  refine ⟨{ θ := ![θ₀, θ₁, θ₁],
            ι := ![θ₀.comp (blk Fld 0), θ₀.comp (blk Fld 1), θ₁.comp (blk Fld 1)],
            left := ?_, right := ?_, comm := ?_ }, rfl, rfl⟩
  · intro i hi
    fin_cases i
    · rfl
    · rw [← q2nPE_blk_zero]
      exact (IsA2Chart.blk_middle h₀ h₁).symm
    · exact absurd hi (by decide)
  · intro i hi
    fin_cases i
    · rfl
    · rfl
    · exact absurd hi (by decide)
  · intro i j hij A B
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact (hcomm A B).eq

private theorem q2nPE_weylMat :
    ((CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
      CFSG.LieType.Steinberg.sl2Upper 1 : SL(2, Fld)) : Matrix (Fin 2) (Fin 2) Fld) =
      !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.sl2Upper, CFSG.LieType.Steinberg.sl2Lower,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem conj_blockSL2_weyl_tv02 [CharP Fld 2] (t : Fld) :
    blockSL2 Fld 3 2 (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1) *
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 2 t *
      (blockSL2 Fld 3 2 (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1))⁻¹ =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 3 t := by
  set w : SL(2, Fld) := CFSG.LieType.Steinberg.sl2Upper 1 *
    CFSG.LieType.Steinberg.sl2Lower (-1) * CFSG.LieType.Steinberg.sl2Upper 1 with hwdef
  set W : SL(4, Fld) := blockSL2 Fld 3 2 w with hWdef
  have hW : (W : Matrix (Fin 4) (Fin 4) Fld) =
      blockMat 4 2 (w : Matrix (Fin 2) (Fin 2) Fld) := by
    rw [hWdef, blockSL2, coe_blockSL]
    rfl
  have hw : (w : Matrix (Fin 2) (Fin 2) Fld) = !![0, 1; -1, 0] := by
    rw [hwdef]
    exact q2nPE_weylMat
  have key : W * CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 2 t * W⁻¹ =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 3 t := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [hW, hw,
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (0 : Fin 4) ≠ 2 by decide),
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (0 : Fin 4) ≠ 3 by decide),
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, CharTwo.neg_eq]
  simpa only [hWdef, hwdef] using key

theorem conj_blockSL2_weyl_tv20 [CharP Fld 2] (t : Fld) :
    blockSL2 Fld 3 2 (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1) *
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 0 t *
      (blockSL2 Fld 3 2 (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1))⁻¹ =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 0 t := by
  set w : SL(2, Fld) := CFSG.LieType.Steinberg.sl2Upper 1 *
    CFSG.LieType.Steinberg.sl2Lower (-1) * CFSG.LieType.Steinberg.sl2Upper 1 with hwdef
  set W : SL(4, Fld) := blockSL2 Fld 3 2 w with hWdef
  have hW : (W : Matrix (Fin 4) (Fin 4) Fld) =
      blockMat 4 2 (w : Matrix (Fin 2) (Fin 2) Fld) := by
    rw [hWdef, blockSL2, coe_blockSL]
    rfl
  have hw : (w : Matrix (Fin 2) (Fin 2) Fld) = !![0, 1; -1, 0] := by
    rw [hwdef]
    exact q2nPE_weylMat
  have key : W * CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 0 t * W⁻¹ =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 0 t := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [hW, hw,
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (2 : Fin 4) ≠ 0 by decide),
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (3 : Fin 4) ≠ 0 by decide),
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, blockMat_apply, CharTwo.neg_eq]
  simpa only [hWdef, hwdef] using key

private theorem q2nPE_tv_adj_up (i : Fin 3) (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld i.castSucc i.succ c =
      blockSL2 Fld 3 i (tv 0 1 c) := by
  rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (Fin.castSucc_lt_succ.ne),
    CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  exact (blockSL2_transvection_up i c).symm

private theorem q2nPE_tv_adj_down (i : Fin 3) (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld i.succ i.castSucc c =
      blockSL2 Fld 3 i (tv 1 0 c) := by
  rw [CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (Fin.castSucc_lt_succ.ne'),
    CFSG.Timmesfeld.tv_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  exact (blockSL2_transvection_down i c).symm

private theorem q2nPE_tv_01 (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 1 c =
      blockSL2 Fld 3 0 (tv 0 1 c) :=
  q2nPE_tv_adj_up (0 : Fin 3) c

private theorem q2nPE_tv_10 (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 0 c =
      blockSL2 Fld 3 0 (tv 1 0 c) :=
  q2nPE_tv_adj_down (0 : Fin 3) c

private theorem q2nPE_tv_12 (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 2 c =
      blockSL2 Fld 3 1 (tv 0 1 c) :=
  q2nPE_tv_adj_up (1 : Fin 3) c

private theorem q2nPE_tv_21 (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 1 c =
      blockSL2 Fld 3 1 (tv 1 0 c) :=
  q2nPE_tv_adj_down (1 : Fin 3) c

private theorem q2nPE_tv_23 (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 3 c =
      blockSL2 Fld 3 2 (tv 0 1 c) :=
  q2nPE_tv_adj_up (2 : Fin 3) c

private theorem q2nPE_tv_32 (c : Fld) :
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 2 c =
      blockSL2 Fld 3 2 (tv 1 0 c) :=
  q2nPE_tv_adj_down (2 : Fin 3) c

private theorem q2nPE_blockSL3_tv02_zero (c : Fld) :
    blockSL3 Fld 3 (0 : Fin 3) (by decide) (tv 0 2 c) =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 2 c := by
  apply Subtype.ext
  rw [blockSL3, coe_blockSL, CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.SpecialLinearGroup.transvection_coe,
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (0 : Fin 4) ≠ 2 by decide),
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]

private theorem q2nPE_blockSL3_tv02_one (c : Fld) :
    blockSL3 Fld 3 (1 : Fin 3) (by decide) (tv 0 2 c) =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 3 c := by
  apply Subtype.ext
  rw [blockSL3, coe_blockSL, CFSG.Timmesfeld.tv_of_ne (show (0 : Fin 3) ≠ 2 by decide),
    Matrix.SpecialLinearGroup.transvection_coe,
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (1 : Fin 4) ≠ 3 by decide),
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]

private theorem q2nPE_blockSL3_tv20_zero (c : Fld) :
    blockSL3 Fld 3 (0 : Fin 3) (by decide) (tv 2 0 c) =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 0 c := by
  apply Subtype.ext
  rw [blockSL3, coe_blockSL, CFSG.Timmesfeld.tv_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.SpecialLinearGroup.transvection_coe,
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (2 : Fin 4) ≠ 0 by decide),
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]

private theorem q2nPE_blockSL3_tv20_one (c : Fld) :
    blockSL3 Fld 3 (1 : Fin 3) (by decide) (tv 2 0 c) =
      CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 1 c := by
  apply Subtype.ext
  rw [blockSL3, coe_blockSL, CFSG.Timmesfeld.tv_of_ne (show (2 : Fin 3) ≠ 0 by decide),
    Matrix.SpecialLinearGroup.transvection_coe,
    CFSG.LieType.Steinberg.CentralExt.SLClosed.tv_of_ne (show (3 : Fin 4) ≠ 1 by decide),
    Matrix.SpecialLinearGroup.transvection_coe]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]

theorem exists_leviA3 [CharP Fld 2] (e : Fin 3 → Fin D.rank)
    (hcart : ∀ k l : Fin 3, D.cartan (e k) (e l) =
      if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0)
    {θ₀ θ₁ : SL(3, Fld) →* K} (h₀ : IsA2Chart M θ₀ (e 0) (e 1)) (h₁ : IsA2Chart M θ₁ (e 1) (e 2))
    (hcomm : ∀ A B : SL(2, Fld), Commute (θ₀ (blk Fld 0 A)) (θ₁ (blk Fld 1 B))) :
    ∃ ε : SL(4, Fld) →* K, ∀ p q : Fin 4, p ≠ q → ∀ c : Fld,
      ε (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld p q c) = M.x (a3Root e p q) c := by
  obtain ⟨F, hF0, hF1⟩ := exists_a3_ctFamily h₀ h₁ hcomm
  obtain ⟨ψ, hψ2, hψ3⟩ := exists_hom_of_ctFamily F
  have hι0 : F.ι 0 = θ₀.comp (blk Fld 0) :=
    (F.left 0 (by decide)).symm.trans (by rw [hF0, ← q2nPE_blk_zero])
  have hι1 : F.ι 1 = θ₀.comp (blk Fld 1) :=
    (F.right 0 (by decide)).symm.trans (by rw [hF0, ← q2nPE_blk_one])
  have hι2 : F.ι 2 = θ₁.comp (blk Fld 1) :=
    (F.right 1 (by decide)).symm.trans (by rw [hF1, ← q2nPE_blk_one])
  have hψι0 : ∀ A : SL(2, Fld), ψ (blockSL2 Fld 3 0 A) = θ₀ (blk Fld 0 A) := by
    intro A
    change (ψ.comp (blockSL2 Fld 3 0)) A = θ₀ (blk Fld 0 A)
    rw [DFunLike.congr_fun (hψ2 0) A, hι0, MonoidHom.comp_apply]
  have hψι1 : ∀ A : SL(2, Fld), ψ (blockSL2 Fld 3 1 A) = θ₀ (blk Fld 1 A) := by
    intro A
    change (ψ.comp (blockSL2 Fld 3 1)) A = θ₀ (blk Fld 1 A)
    rw [DFunLike.congr_fun (hψ2 1) A, hι1, MonoidHom.comp_apply]
  have hψι2 : ∀ A : SL(2, Fld), ψ (blockSL2 Fld 3 2 A) = θ₁ (blk Fld 1 A) := by
    intro A
    change (ψ.comp (blockSL2 Fld 3 2)) A = θ₁ (blk Fld 1 A)
    rw [DFunLike.congr_fun (hψ2 2) A, hι2, MonoidHom.comp_apply]
  have h02 : ∀ c, ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 2 c) =
      M.x (Pi.single (e 0) 1 + Pi.single (e 1) 1) c := by
    intro c
    rw [← q2nPE_blockSL3_tv02_zero c]
    change (ψ.comp (blockSL3 Fld 3 (0 : Fin 3) (by decide))) (tv 0 2 c) =
      M.x (Pi.single (e 0) 1 + Pi.single (e 1) 1) c
    rw [DFunLike.congr_fun (hψ3 0 (by decide)) (tv 0 2 c), hF0, (h₀ c).2.2.2.2.1]
  have h20 : ∀ c, ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 0 c) =
      M.x (-(Pi.single (e 0) 1 + Pi.single (e 1) 1)) c := by
    intro c
    rw [← q2nPE_blockSL3_tv20_zero c]
    change (ψ.comp (blockSL3 Fld 3 (0 : Fin 3) (by decide))) (tv 2 0 c) =
      M.x (-(Pi.single (e 0) 1 + Pi.single (e 1) 1)) c
    rw [DFunLike.congr_fun (hψ3 0 (by decide)) (tv 2 0 c), hF0, (h₀ c).2.2.2.2.2]
  have h13 : ∀ c, ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 3 c) =
      M.x (Pi.single (e 1) 1 + Pi.single (e 2) 1) c := by
    intro c
    rw [← q2nPE_blockSL3_tv02_one c]
    change (ψ.comp (blockSL3 Fld 3 (1 : Fin 3) (by decide))) (tv 0 2 c) =
      M.x (Pi.single (e 1) 1 + Pi.single (e 2) 1) c
    rw [DFunLike.congr_fun (hψ3 1 (by decide)) (tv 0 2 c), hF1, (h₁ c).2.2.2.2.1]
  have h31 : ∀ c, ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 1 c) =
      M.x (-(Pi.single (e 1) 1 + Pi.single (e 2) 1)) c := by
    intro c
    rw [← q2nPE_blockSL3_tv20_one c]
    change (ψ.comp (blockSL3 Fld 3 (1 : Fin 3) (by decide))) (tv 2 0 c) =
      M.x (-(Pi.single (e 1) 1 + Pi.single (e 2) 1)) c
    rw [DFunLike.congr_fun (hψ3 1 (by decide)) (tv 2 0 c), hF1, (h₁ c).2.2.2.2.2]
  have hWn : ψ (blockSL2 Fld 3 2
      (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1)) = n (e 2) := by
    change (ψ.comp (blockSL2 Fld 3 2))
      (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1) = n (e 2)
    rw [DFunLike.congr_fun (hψ2 2) _, hι2]
    change θ₁ (blk Fld 1 (CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1)) = n (e 2)
    have hblk : blk Fld 1 (CFSG.LieType.Steinberg.sl2Upper 1 *
        CFSG.LieType.Steinberg.sl2Lower (-1) *
        CFSG.LieType.Steinberg.sl2Upper 1) = tv 1 2 1 * tv 2 1 (-1) * tv 1 2 1 := by
      rw [← CFSG.Timmesfeld.LevisExtras.tv01_eq_sl2Upper (1 : Fld),
        ← CFSG.Timmesfeld.LevisExtras.tv10_eq_sl2Lower (-1 : Fld),
        map_mul, map_mul, blk_one_tv01, blk_one_tv10]
    rw [hblk, map_mul, map_mul, (h₁ 1).2.2.1, (h₁ (-1)).2.2.2.1]
    exact (M.nm_def (e 2)).symm
  have hcart01 : D.cartan (e 0) (e 1) = -1 := by simpa using hcart 0 1
  have hcart20 : D.cartan (e 2) (e 0) = 0 := by simpa using hcart 2 0
  have hcart21 : D.cartan (e 2) (e 1) = -1 := by simpa using hcart 2 1
  have hγmem : (Pi.single (e 0) 1 + Pi.single (e 1) 1 : Fin D.rank → ℤ) ∈ D.roots := by
    have hroot := weylAction_mem_roots (hA := D.isFiniteType) (D := D.divisible)
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (e 0))
      (CFSG.Timmesfeld.LevisExtras.single_mem_roots (e 1))
    convert hroot using 1
    rw [weylAction_simple, reflection_apply]
    have hsum : (∑ j, D.cartan (e 0) j * (Pi.single (e 1) (1 : ℤ) : Fin D.rank → ℤ) j) = -1 := by
      rw [Finset.sum_eq_single (e 1) (fun j _ hj => by
          rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun hmem => absurd (Finset.mem_univ (e 1)) hmem)]
      rw [Pi.single_eq_same, mul_one, hcart01]
    rw [hsum, neg_one_smul]
    abel
  have hweyl : weylAction D.isFiniteType
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple (e 2))
      (Pi.single (e 0) 1 + Pi.single (e 1) 1) =
      Pi.single (e 0) 1 + Pi.single (e 1) 1 + Pi.single (e 2) 1 := by
    rw [weylAction_simple, reflection_apply]
    have hs0 : (∑ j, D.cartan (e 2) j * (Pi.single (e 0) (1 : ℤ) : Fin D.rank → ℤ) j) = 0 := by
      rw [Finset.sum_eq_single (e 0) (fun j _ hj => by
          rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun hmem => absurd (Finset.mem_univ (e 0)) hmem)]
      rw [Pi.single_eq_same, mul_one, hcart20]
    have hs1 : (∑ j, D.cartan (e 2) j * (Pi.single (e 1) (1 : ℤ) : Fin D.rank → ℤ) j) = -1 := by
      rw [Finset.sum_eq_single (e 1) (fun j _ hj => by
          rw [Pi.single_eq_of_ne hj, mul_zero])
        (fun hmem => absurd (Finset.mem_univ (e 1)) hmem)]
      rw [Pi.single_eq_same, mul_one, hcart21]
    have hsum : (∑ j, D.cartan (e 2) j *
        ((Pi.single (e 0) (1 : ℤ) + Pi.single (e 1) (1 : ℤ)) : Fin D.rank → ℤ) j) = -1 := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hs0, hs1, zero_add]
    rw [hsum, neg_one_smul, sub_neg_eq_add]
  have h03 : ∀ c, ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 3 c) =
      M.x (Pi.single (e 0) 1 + Pi.single (e 1) 1 + Pi.single (e 2) 1) c := by
    intro c
    rw [← conj_blockSL2_weyl_tv02 c]
    rw [map_mul, map_mul, map_inv, hWn, h02 c, M.nm_conj (e 2) _ hγmem c, hweyl]
  have h30 : ∀ c, ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 0 c) =
      M.x (-(Pi.single (e 0) 1 + Pi.single (e 1) 1 + Pi.single (e 2) 1)) c := by
    intro c
    rw [← conj_blockSL2_weyl_tv20 c]
    rw [map_mul, map_mul, map_inv, hWn, h20 c,
      M.nm_conj (e 2) _ (CFSG.Timmesfeld.LevisExtras.neg_mem_roots hγmem) c]
    rw [map_neg, hweyl]
  refine ⟨ψ, ?_⟩
  intro p q hpq c
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 1 c) =
      M.x (a3Root e (0 : Fin 4) (1 : Fin 4)) c
    rw [q2nPE_tv_01 c, hψι0 (tv 0 1 c), blk_zero_tv01, (h₀ c).1]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 2 c) =
      M.x (a3Root e (0 : Fin 4) (2 : Fin 4)) c
    rw [h02 c]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (0 : Fin 4) 3 c) =
      M.x (a3Root e (0 : Fin 4) (3 : Fin 4)) c
    rw [h03 c]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 0 c) =
      M.x (a3Root e (1 : Fin 4) (0 : Fin 4)) c
    rw [q2nPE_tv_10 c, hψι0 (tv 1 0 c), blk_zero_tv10, (h₀ c).2.1]
    simp [a3Root, Fin.sum_univ_three]
  · exact absurd rfl hpq
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 2 c) =
      M.x (a3Root e (1 : Fin 4) (2 : Fin 4)) c
    rw [q2nPE_tv_12 c, hψι1 (tv 0 1 c), blk_one_tv01, (h₀ c).2.2.1]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (1 : Fin 4) 3 c) =
      M.x (a3Root e (1 : Fin 4) (3 : Fin 4)) c
    rw [h13 c]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 0 c) =
      M.x (a3Root e (2 : Fin 4) (0 : Fin 4)) c
    rw [h20 c]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 1 c) =
      M.x (a3Root e (2 : Fin 4) (1 : Fin 4)) c
    rw [q2nPE_tv_21 c, hψι1 (tv 1 0 c), blk_one_tv10, (h₀ c).2.2.2.1]
    simp [a3Root, Fin.sum_univ_three]
  · exact absurd rfl hpq
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (2 : Fin 4) 3 c) =
      M.x (a3Root e (2 : Fin 4) (3 : Fin 4)) c
    rw [q2nPE_tv_23 c, hψι2 (tv 0 1 c), blk_one_tv01, (h₁ c).2.2.1]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 0 c) =
      M.x (a3Root e (3 : Fin 4) (0 : Fin 4)) c
    rw [h30 c]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 1 c) =
      M.x (a3Root e (3 : Fin 4) (1 : Fin 4)) c
    rw [h31 c]
    simp [a3Root, Fin.sum_univ_three]
  · change ψ (CFSG.LieType.Steinberg.CentralExt.SLClosed.tv Fld (3 : Fin 4) 2 c) =
      M.x (a3Root e (3 : Fin 4) (2 : Fin 4)) c
    rw [q2nPE_tv_32 c, hψι2 (tv 1 0 c), blk_one_tv10, (h₁ c).2.2.2.1]
    simp [a3Root, Fin.sum_univ_three]
  · exact absurd rfl hpq

end CFSG.ClassicalInvolution.Phan.PhanE
