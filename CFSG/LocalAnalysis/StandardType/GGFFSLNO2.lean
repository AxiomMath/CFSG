module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs
import CFSG.RankThree.PartOne.TAIL.LSideOutAut
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFGF4
import CFSG.Quasithin.Vol2.Ch11SecA02Simple
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.NoncommRing
import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
import CFSG.Dihedral.FourgroupCycleControl
import CFSG.Dihedral.OriginalCentralizerOddCore
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.TAIL.KSideCen
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.RankThree.PartOne.TAIL
open CFSG.Quasithin.Vol2.Ch11.SecA
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open Matrix

private theorem mat_add_self {n : ℕ} (X : Matrix (Fin n) (Fin n) (ZMod 2)) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (X i j)

private theorem det_eq_one_of_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : A * A = 1) : A.det = 1 := by
  have h1 : A.det * A.det = 1 := by
    have := congrArg Matrix.det h
    rwa [Matrix.det_mul, Matrix.det_one] at this
  have h2 : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide
  exact h2 A.det h1

private theorem vecMulVec_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (c d : Fin n → ZMod 2) :
    Matrix.vecMulVec c d * A = Matrix.vecMulVec c (d ᵥ* A) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul_apply,
    Matrix.col_apply, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem vecMulVec_mulVec' {n : ℕ} (c d v : Fin n → ZMod 2) :
    Matrix.vecMulVec c d *ᵥ v = (d ⬝ᵥ v) • c := by
  rw [Matrix.vecMulVec_mulVec]
  exact IsCentralScalar.op_smul_eq_smul _ _

private def tmat {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (c : Fin n → ZMod 2) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  1 + Matrix.vecMulVec c (A *ᵥ c)

private theorem tmat_mul_self {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (c : Fin n → ZMod 2) (hc : c ⬝ᵥ (A *ᵥ c) = 0) :
    tmat A c * tmat A c = 1 := by
  have hX : Matrix.vecMulVec c (A *ᵥ c) * Matrix.vecMulVec c (A *ᵥ c) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm (A *ᵥ c) c, hc, zero_smul]
    simp
  simp only [tmat, add_mul, mul_add, one_mul, mul_one, hX, add_zero]
  rw [add_assoc, mat_add_self, add_zero]

private theorem tmat_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hAsym : Aᵀ = A)
    (c v : Fin n → ZMod 2) :
    tmat A c *ᵥ v = v + (c ⬝ᵥ (A *ᵥ v)) • c := by
  have hA : c ᵥ* A = A *ᵥ c := by
    conv_lhs => rw [← hAsym]
    rw [Matrix.vecMul_transpose]
  have h : c ⬝ᵥ (A *ᵥ v) = (A *ᵥ c) ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, hA]
  simp only [tmat, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec', h]

private theorem tmat_isometry {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA2 : A * A = 1) (hAsym : Aᵀ = A) (c : Fin n → ZMod 2)
    (hc : c ⬝ᵥ (A *ᵥ c) = 0) :
    tmat A c * A * (tmat A c)ᵀ = A := by
  set d := A *ᵥ c with hd
  have hc' : c ⬝ᵥ d = 0 := hc
  have hdA : d ᵥ* A = c := by
    calc d ᵥ* A = d ᵥ* Aᵀ := by rw [hAsym]
      _ = A *ᵥ d := Matrix.vecMul_transpose A d
      _ = A *ᵥ (A *ᵥ c) := by rw [hd]
      _ = (A * A) *ᵥ c := Matrix.mulVec_mulVec c A A
      _ = 1 *ᵥ c := by rw [hA2]
      _ = c := Matrix.one_mulVec c
  have hXmul : Matrix.vecMulVec c d * A = Matrix.vecMulVec c c := by
    rw [vecMulVec_mul, hdA]
  have hAmul : A * (Matrix.vecMulVec c d)ᵀ = Matrix.vecMulVec c c := by
    rw [Matrix.transpose_vecMulVec, Matrix.mul_vecMulVec, hd]
    congr 1
    calc A *ᵥ (A *ᵥ c) = (A * A) *ᵥ c := Matrix.mulVec_mulVec c A A
      _ = 1 *ᵥ c := by rw [hA2]
      _ = c := Matrix.one_mulVec c
  have hXX : Matrix.vecMulVec c d * A * (Matrix.vecMulVec c d)ᵀ = 0 := by
    rw [hXmul, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
      hc', zero_smul]
    simp
  have hExp : tmat A c * A * (tmat A c)ᵀ =
      A + Matrix.vecMulVec c d * A + A * (Matrix.vecMulVec c d)ᵀ +
        Matrix.vecMulVec c d * A * (Matrix.vecMulVec c d)ᵀ := by
    rw [tmat, ← hd]
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]
    noncomm_ring
  rw [hExp, hXX, hXmul, hAmul, add_zero]
  rw [add_assoc, mat_add_self, add_zero]
private def J2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

private def A6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0]

private def A7 : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1]

private def e6 : Fin 6 ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin 2 where
  toFun := ![.inl (.inl 0), .inl (.inl 1), .inl (.inr 0), .inl (.inr 1), .inr 0, .inr 1]
  invFun := fun x =>
    match x with
    | .inl (.inl i) => ![0, 1] i
    | .inl (.inr i) => ![2, 3] i
    | .inr i => ![4, 5] i
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

private theorem bl_e6_t1M :
    bl e6 W6.t1M = fromBlocks (fromBlocks rhoM 0 0 1) 0 0 1 := by decide +kernel

private theorem bl_e6_t1Mi :
    bl e6 W6.t1Mi = fromBlocks (fromBlocks (rhoM * rhoM) 0 0 1) 0 0 1 := by
  decide +kernel

private theorem bl_e6_t2M :
    bl e6 W6.t2M = fromBlocks (fromBlocks 1 0 0 rhoM) 0 0 1 := by decide +kernel

private theorem bl_e6_t2Mi :
    bl e6 W6.t2Mi = fromBlocks (fromBlocks 1 0 0 (rhoM * rhoM)) 0 0 1 := by
  decide +kernel

private theorem bl_e6_t3M :
    bl e6 W6.t3M = fromBlocks 1 0 0 rhoM := by decide +kernel

private theorem bl_e6_t3Mi :
    bl e6 W6.t3Mi = fromBlocks 1 0 0 (rhoM * rhoM) := by decide +kernel

private theorem bl_e6_t3M_add_sq :
    bl e6 (W6.t3M + W6.t3M ^ 2) = fromBlocks 0 0 0 1 := by decide +kernel

private theorem t3Mi_add_sq : W6.t3Mi + W6.t3Mi ^ 2 = W6.t3M + W6.t3M ^ 2 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem eq_J_of (X : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hsym : Xᵀ = X)
    (h : X * (rhoM * rhoM) = rhoM * X) (hne : X ≠ 0) : X = J2 := by
  revert X
  decide +kernel

private theorem A6_transpose : A6ᵀ = A6 := by decide +kernel

private theorem A6_mul_self : A6 * A6 = 1 := by decide +kernel

private theorem A6_det : A6.det = 1 := det_eq_one_of_sq A6_mul_self

private theorem bl_e6_A6 :
    bl e6 A6 = fromBlocks (fromBlocks J2 0 0 J2) 0 0 J2 := by decide +kernel

private theorem A7_transpose : A7ᵀ = A7 := by decide +kernel

private theorem A7_mul_self : A7 * A7 = 1 := by decide +kernel

private def e7 : Fin 7 ≃ Fin 6 ⊕ Fin 1 where
  toFun := ![.inl 0, .inl 1, .inl 2, .inl 3, .inl 4, .inl 5, .inr 0]
  invFun := fun x =>
    match x with
    | .inl i => ![0, 1, 2, 3, 4, 5] i
    | .inr _ => 6
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; cases x with
    | inl i => revert i; decide
    | inr i => revert i; decide

set_option maxRecDepth 10000 in
private theorem bl_e7_A7 : bl e7 A7 = fromBlocks A6 0 0 1 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bl_e7_t1M : bl e7 W7.t1M = fromBlocks W6.t1M 0 0 1 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bl_e7_t1Mi : bl e7 W7.t1Mi = fromBlocks W6.t1Mi 0 0 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bl_e7_t2M : bl e7 W7.t2M = fromBlocks W6.t2M 0 0 1 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bl_e7_t2Mi : bl e7 W7.t2Mi = fromBlocks W6.t2Mi 0 0 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem bl_e7_t3M : bl e7 W7.t3M = fromBlocks W6.t3M 0 0 1 := by decide +kernel

set_option maxRecDepth 10000 in
private theorem bl_e7_t3Mi : bl e7 W7.t3Mi = fromBlocks W6.t3Mi 0 0 1 := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem fromBlocks_rhoMi_add_sq :
    (fromBlocks (rhoM * rhoM) 0 0 1 +
      (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (fromBlocks rhoM 0 0 1 + (fromBlocks rhoM 0 0 1) ^ 2 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem fromBlocks_rho_add_sq :
    (fromBlocks rhoM 0 0 1 + (fromBlocks rhoM 0 0 1) ^ 2 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by decide +kernel

set_option maxRecDepth 10000 in
private theorem fromBlocks_split :
    (fromBlocks (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 1 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      (1 + fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by decide +kernel

private theorem eq_A6 {A : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hsym : Aᵀ = A) (hdet : A.det ≠ 0)
    (h1 : A * W6.t1Mi = W6.t1M * A) (h2 : A * W6.t2Mi = W6.t2M * A)
    (h3 : A * W6.t3Mi = W6.t3M * A) : A = A6 := by
  have hP3' : A * (W6.t3Mi + W6.t3Mi ^ 2) = (W6.t3Mi + W6.t3Mi ^ 2) * A := by
    calc A * (W6.t3Mi + W6.t3Mi ^ 2)
        = A * W6.t3Mi + A * W6.t3Mi ^ 2 := mul_add _ _ _
      _ = W6.t3M * A + A * W6.t3Mi ^ 2 := by rw [h3]
      _ = W6.t3M * A + (A * W6.t3Mi) * W6.t3Mi := by rw [pow_two, ← mul_assoc]
      _ = W6.t3M * A + (W6.t3M * A) * W6.t3Mi := by rw [h3]
      _ = W6.t3M * A + W6.t3M * (A * W6.t3Mi) := by rw [mul_assoc]
      _ = W6.t3M * A + W6.t3M * (W6.t3M * A) := by rw [h3]
      _ = W6.t3M * A + (W6.t3M * W6.t3M) * A := by rw [← mul_assoc]
      _ = (W6.t3M + W6.t3M ^ 2) * A := by rw [pow_two, add_mul]
      _ = (W6.t3Mi + W6.t3Mi ^ 2) * A := by rw [← t3Mi_add_sq]
  have hP3 : A * (W6.t3M + W6.t3M ^ 2) = (W6.t3M + W6.t3M ^ 2) * A := by
    rwa [t3Mi_add_sq] at hP3' 
  have hbd : IsBlockDiag (bl e6 A) := by
    apply isBlockDiag_of_commute
    have h := bl_commute e6 hP3
    rwa [bl_e6_t3M_add_sq] at h
  obtain ⟨X4, X2, hXeq⟩ : ∃ X4 X2, bl e6 A = fromBlocks X4 0 0 X2 :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag hbd⟩
  have hsymbl : (bl e6 A)ᵀ = bl e6 A := by rw [← bl_transpose, hsym]
  rw [hXeq, fromBlocks_diag_transpose] at hsymbl
  obtain ⟨hX4sym, -, -, hX2sym⟩ := fromBlocks_inj.mp hsymbl
  have hdetbl : (bl e6 A).det = A.det :=
    Matrix.det_submatrix_equiv_self e6.symm A
  have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hdet1 : A.det = 1 := hz A.det hdet
  have hprod : X4.det * X2.det = 1 := by
    have h := hdetbl
    rw [hXeq, Matrix.det_fromBlocks_zero₁₂, hdet1] at h
    exact h
  have hX2det : X2.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact zero_ne_one hprod
  have hX2ne : X2 ≠ 0 := by
    intro h0
    apply hX2det
    rw [h0]
    exact Matrix.det_zero
  have hrel3 : X2 * (rhoM * rhoM) = rhoM * X2 := by
    have h' : bl e6 A * bl e6 W6.t3Mi = bl e6 W6.t3M * bl e6 A := by
      rw [← bl_mul, ← bl_mul, h3]
    rw [hXeq, bl_e6_t3Mi, bl_e6_t3M, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
    exact (fromBlocks_inj.mp h').2.2.2
  have hX2J : X2 = J2 := eq_J_of X2 hX2sym hrel3 hX2ne
  have hrel_t1 : X4 * fromBlocks (rhoM * rhoM) 0 0 1 =
      fromBlocks rhoM 0 0 1 * X4 := by
    have h' : bl e6 A * bl e6 W6.t1Mi = bl e6 W6.t1M * bl e6 A := by
      rw [← bl_mul, ← bl_mul, h1]
    rw [hXeq, bl_e6_t1Mi, bl_e6_t1M, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
    exact (fromBlocks_inj.mp h').1
  have hrel_t2 : X4 * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 (rhoM * rhoM) =
      fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 rhoM * X4 := by
    have h' : bl e6 A * bl e6 W6.t2Mi = bl e6 W6.t2M * bl e6 A := by
      rw [← bl_mul, ← bl_mul, h2]
    rw [hXeq, bl_e6_t2Mi, bl_e6_t2M, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
    exact (fromBlocks_inj.mp h').1
  have hR' := fromBlocks_rhoMi_add_sq
  have hproj1 := fromBlocks_rho_add_sq
  have hP1 : X4 * (fromBlocks rhoM 0 0 1 + (fromBlocks rhoM 0 0 1) ^ 2) =
      (fromBlocks rhoM 0 0 1 + (fromBlocks rhoM 0 0 1) ^ 2) * X4 := by
    have hP1' : X4 * (fromBlocks (rhoM * rhoM) 0 0 1 +
        (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2) =
        (fromBlocks (rhoM * rhoM) 0 0 1 + (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2) * X4 := by
      calc X4 * (fromBlocks (rhoM * rhoM) 0 0 1 + (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2)
          = X4 * fromBlocks (rhoM * rhoM) 0 0 1 +
              X4 * (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2 := mul_add _ _ _
        _ = fromBlocks rhoM 0 0 1 * X4 +
              X4 * (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2 := by rw [hrel_t1]
        _ = fromBlocks rhoM 0 0 1 * X4 +
              (X4 * fromBlocks (rhoM * rhoM) 0 0 1) *
                fromBlocks (rhoM * rhoM) 0 0 1 := by rw [pow_two, ← mul_assoc]
        _ = fromBlocks rhoM 0 0 1 * X4 +
              (fromBlocks rhoM 0 0 1 * X4) * fromBlocks (rhoM * rhoM) 0 0 1 := by
              rw [hrel_t1]
        _ = fromBlocks rhoM 0 0 1 * X4 +
              fromBlocks rhoM 0 0 1 * (X4 * fromBlocks (rhoM * rhoM) 0 0 1) := by
              rw [mul_assoc]
        _ = fromBlocks rhoM 0 0 1 * X4 +
              fromBlocks rhoM 0 0 1 * (fromBlocks rhoM 0 0 1 * X4) := by rw [hrel_t1]
        _ = fromBlocks rhoM 0 0 1 * X4 +
              (fromBlocks rhoM 0 0 1 * fromBlocks rhoM 0 0 1) * X4 := by
              rw [← mul_assoc]
        _ = (fromBlocks rhoM 0 0 1 + (fromBlocks rhoM 0 0 1) ^ 2) * X4 := by
              rw [pow_two, add_mul]
        _ = (fromBlocks (rhoM * rhoM) 0 0 1 +
              (fromBlocks (rhoM * rhoM) 0 0 1) ^ 2) * X4 := by rw [← hR']
    rwa [hR'] at hP1' 
  have hPα : X4 * fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 0 =
      fromBlocks (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 0 * X4 := by
    rw [← hproj1]
    exact hP1
  have hsplit := fromBlocks_split
  have hPβ : X4 * fromBlocks (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 1 =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0 1 * X4 := by
    rw [hsplit, mul_add, mul_one, add_mul, one_mul, hPα]
  have hbdX4 : IsBlockDiag X4 := isBlockDiag_of_commute hPβ
  obtain ⟨X0, X1, hX4eq⟩ : ∃ X0 X1, X4 = fromBlocks X0 0 0 X1 :=
    ⟨_, _, eq_fromBlocks_of_isBlockDiag hbdX4⟩
  have hX4sym' : X4ᵀ = X4 := hX4sym
  rw [hX4eq, fromBlocks_diag_transpose] at hX4sym'
  obtain ⟨hX0sym, -, -, hX1sym⟩ := fromBlocks_inj.mp hX4sym'
  have hX4det : X4.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact zero_ne_one hprod
  have hprod01 : X0.det * X1.det ≠ 0 := by
    intro h0
    apply hX4det
    rw [hX4eq, Matrix.det_fromBlocks_zero₁₂, h0]
  have hX0det : X0.det ≠ 0 := by
    intro h0
    exact hprod01 (by rw [h0, zero_mul])
  have hX1det : X1.det ≠ 0 := by
    intro h0
    exact hprod01 (by rw [h0, mul_zero])
  have hX0ne : X0 ≠ 0 := by
    intro h0
    apply hX0det
    rw [h0]
    exact Matrix.det_zero
  have hX1ne : X1 ≠ 0 := by
    intro h0
    apply hX1det
    rw [h0]
    exact Matrix.det_zero
  have hX0rel : X0 * (rhoM * rhoM) = rhoM * X0 := by
    have h := hrel_t1
    rw [hX4eq, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).1
  have hX1rel : X1 * (rhoM * rhoM) = rhoM * X1 := by
    have h := hrel_t2
    rw [hX4eq, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have hX0J : X0 = J2 := eq_J_of X0 hX0sym hX0rel hX0ne
  have hX1J : X1 = J2 := eq_J_of X1 hX1sym hX1rel hX1ne
  have hX4J : X4 = fromBlocks J2 0 0 J2 := by rw [hX4eq, hX0J, hX1J]
  apply bl_injective e6
  rw [hXeq, hX4J, hX2J, bl_e6_A6]

private theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnc : ¬ IsMulCommutative G) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc

private theorem eq_one_of_mem_center {G : Type*} [Group G] {H : Subgroup G} (h : H = ⊥)
    {x : G} (hx : x ∈ H) : x = 1 := by
  rw [h] at hx
  exact Subgroup.mem_bot.mp hx

private theorem conj_mulAut_conj {G : Type*} [Group G] (δ : MulAut G) (g : G) :
    δ * MulAut.conj g * δ⁻¹ = MulAut.conj (δ g) := by
  ext y
  change δ (g * δ.symm y * g⁻¹) = δ g * y * (δ g)⁻¹
  rw [map_mul, map_mul, map_inv, δ.apply_symm_apply]

private theorem slGraphAut_mul_self (n : ℕ) :
    slGraphAut n (ZMod 2) * slGraphAut n (ZMod 2) = 1 :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.slGraph_mul_slGraph

private theorem slGraphAut_inv (n : ℕ) : (slGraphAut n (ZMod 2))⁻¹ = slGraphAut n (ZMod 2) :=
  inv_eq_of_mul_eq_one_right (slGraphAut_mul_self n)

private theorem not_comm_SL6 : ¬ IsMulCommutative SL(6, ZMod 2) := by
  intro h
  have h' : W6.s1 * W6.T 0 = W6.T 0 * W6.s1 := h.is_comm.comm W6.s1 (W6.T 0)
  have h'' := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h'
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, W6.coe_T] at h''
  exact absurd h'' (by decide +kernel)

private theorem not_comm_SL7 : ¬ IsMulCommutative SL(7, ZMod 2) := by
  intro h
  have h' : W7.s1 * W7.T 0 = W7.T 0 * W7.s1 := h.is_comm.comm W7.s1 (W7.T 0)
  have h'' := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h'
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, W7.coe_T] at h''
  exact absurd h'' (by decide +kernel)

private theorem orderOf_T0_SL6 : orderOf (W6.T 0) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (W6.pow_T 0) ?_
  intro h
  have h' := congrArg (fun z : SL(6, ZMod 2) => (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  rw [Matrix.SpecialLinearGroup.coe_one, W6.coe_T] at h'
  exact absurd h' (by decide +kernel)

private theorem orderOf_T0_SL7 : orderOf (W7.T 0) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (W7.pow_T 0) ?_
  intro h
  have h' := congrArg (fun z : SL(7, ZMod 2) => (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) h
  rw [Matrix.SpecialLinearGroup.coe_one, W7.coe_T] at h'
  exact absurd h' (by decide +kernel)

private theorem inv_eq_pow_two_of_cube {G : Type*} [Group G] {x : G} (h : x ^ 3 = 1) :
    x⁻¹ = x ^ 2 :=
  inv_eq_of_mul_eq_one_left (by rw [← pow_succ, h])

private theorem inv_T0_SL6 : ((W6.T 0)⁻¹ : SL(6, ZMod 2)) = W6.T 0 ^ 2 :=
  inv_eq_pow_two_of_cube (x := W6.T 0) (W6.pow_T 0)

private theorem inv_T1_SL6 : ((W6.T 1)⁻¹ : SL(6, ZMod 2)) = W6.T 1 ^ 2 :=
  inv_eq_pow_two_of_cube (x := W6.T 1) (W6.pow_T 1)

private theorem inv_T2_SL6 : ((W6.T 2)⁻¹ : SL(6, ZMod 2)) = W6.T 2 ^ 2 :=
  inv_eq_pow_two_of_cube (x := W6.T 2) (W6.pow_T 2)

private theorem t1M_sq_transpose : (W6.t1M ^ 2)ᵀ = W6.t1Mi := by decide +kernel

private theorem t2M_sq_transpose : (W6.t2M ^ 2)ᵀ = W6.t2Mi := by decide +kernel

private theorem t3M_sq_transpose : (W6.t3M ^ 2)ᵀ = W6.t3Mi := by decide +kernel

private theorem mul_transpose_eq_of_fixed {n : ℕ} {g x : SL(n, ZMod 2)}
    (h : MulAut.conj g (slGraphAut n (ZMod 2) x) = x) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (((x⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ =
      (x : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have hm : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (((x⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *
        (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) =
      (x : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    have h' := congrArg (fun z : SL(n, ZMod 2) => (z : Matrix (Fin n) (Fin n) (ZMod 2))) h
    rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul,
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix] at h'
    exact h'
  have hGG' : (((g * g⁻¹ : SL(n, ZMod 2)) : SL(n, ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hG'G : (((g⁻¹ * g : SL(n, ZMod 2)) : SL(n, ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hGG'' : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hGG']
  have hG'G' : (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hG'G]
  calc (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (((x⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ
      = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (((x⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ * 1 := by
            rw [Matrix.mul_one]
    _ = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (((x⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *
            (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (g : Matrix (Fin n) (Fin n) (ZMod 2))) := by rw [hG'G']
    _ = ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (((x⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *
            (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))) *
              (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by noncomm_ring
    _ = (x : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by rw [hm]
private theorem vecElt_pow_three {H : Type*} [Group H] {z : Fin 3 → H} {t : H}
    (hf : CFSG.RankThree.PartTwo.Sec4.Item434Kit.WreathFacts z t) (v : Fin 3 → ZMod 3) :
    vecElt z v ^ 3 = 1 := by
  have hv : v + v + v = 0 := by
    ext i
    have h : ∀ x : ZMod 3, x + x + x = 0 := by decide
    exact h (v i)
  calc vecElt z v ^ 3 = vecElt z v ^ 2 * vecElt z v := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
    _ = (vecElt z v * vecElt z v) * vecElt z v := by rw [pow_two]
    _ = vecElt z (v + v) * vecElt z v := by
          rw [← CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_add hf]
    _ = vecElt z (v + v + v) := by
          rw [← CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_add hf]
    _ = vecElt z 0 := by rw [hv]
    _ = 1 := by simp [vecElt]

private theorem matrix_eq_of_fixed {n : ℕ} {g y : SL(n, ZMod 2)}
    (h : MulAut.conj g (slGraphAut n (ZMod 2) y) = y) :
    (y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have h1 := mul_transpose_eq_of_fixed h
  have hYY' : (y : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h3 : (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *
      (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hYY', Matrix.transpose_one]
  calc (y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
      = ((y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2))) *
          (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := rfl
    _ = ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ) *
            (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by rw [← h1]
    _ = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          ((((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *
            (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) := by rw [Matrix.mul_assoc]
    _ = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * 1 := by rw [h3]
    _ = (g : Matrix (Fin n) (Fin n) (ZMod 2)) := Matrix.mul_one _

private theorem fixed_of_matrix_eq {n : ℕ} {g y : SL(n, ZMod 2)}
    (hGsym : (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)))
    (h : (y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      (g : Matrix (Fin n) (Fin n) (ZMod 2))) :
    MulAut.conj g (slGraphAut n (ZMod 2) y) = y := by
  have hY'Y : (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
      (y : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hGG' : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hGY : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
        (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
          (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    calc (g : Matrix (Fin n) (Fin n) (ZMod 2)) * (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
        = (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
            (y : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
                (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
          rw [hY'Y, Matrix.one_mul]
      _ = (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
            ((y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (y : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) := by noncomm_ring
      _ = (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
            (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by rw [h]
  have hGY' : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ =
        (y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    have h' := congrArg Matrix.transpose hGY
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hGsym] at h'
    exact h'.symm
  apply Subtype.ext
  have hm : ((MulAut.conj g (slGraphAut n (ZMod 2) y) : SL(n, ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = (y : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul,
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
    calc (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          (((y⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ *
            (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))
        = ((y : Matrix (Fin n) (Fin n) (ZMod 2)) * (g : Matrix (Fin n) (Fin n) (ZMod 2))) *
            (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) := by rw [hGY']
      _ = (y : Matrix (Fin n) (Fin n) (ZMod 2)) *
            ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (((g⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))) := by
            rw [Matrix.mul_assoc]
      _ = (y : Matrix (Fin n) (Fin n) (ZMod 2)) * 1 := by rw [hGG']
      _ = (y : Matrix (Fin n) (Fin n) (ZMod 2)) := Matrix.mul_one _
  exact hm

private def transElem6 (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0) : SL(6, ZMod 2) :=
  ⟨tmat A6 c, detOne_of_mul_eq_one (tmat_mul_self A6 c hc)⟩

private theorem coe_transElem6 (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0) :
    ((transElem6 c hc : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = tmat A6 c := rfl

private theorem transElem6_mul_self (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0) :
    transElem6 c hc * transElem6 c hc = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_transElem6,
    tmat_mul_self A6 c hc]

private theorem transElem6_smul (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0)
    (v : Fin 6 → ZMod 2) :
    (transElem6 c hc : SL(6, ZMod 2)) • v =
      v + (c ⬝ᵥ (A6 *ᵥ v)) • c := by
  change tmat A6 c *ᵥ v = v + (c ⬝ᵥ (A6 *ᵥ v)) • c
  rw [tmat_mulVec A6 A6_transpose]

private theorem transElem6_fixed {σ : MulAut SL(6, ZMod 2)} {g : SL(6, ZMod 2)}
    (hσ : σ = MulAut.conj g * slGraphAut 6 (ZMod 2))
    (hG : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = A6)
    (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0) :
    σ (transElem6 c hc) = transElem6 c hc := by
  rw [hσ, MulAut.mul_apply]
  apply fixed_of_matrix_eq
  · rw [hG]; exact A6_transpose
  · rw [coe_transElem6, hG]
    exact tmat_isometry A6 A6_mul_self A6_transpose c hc

private theorem mem_normalizer_of_conj_le {G : Type*} [Group G] {H : Subgroup G} {t : G}
    (ht : t * t = 1) (h : ∀ x ∈ H, t * x * t⁻¹ ∈ H) :
    t ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hx' : t * (t * x * t) * t ∈ H := by
      have h0 := h (t * x * t⁻¹) hx
      rwa [ht'] at h0
    rw [show x = t * (t * x * t) * t from by
      calc x = (t * t) * x * (t * t) := by rw [ht, one_mul, mul_one]
        _ = t * (t * x * t) * t := by noncomm_ring]
    exact hx'

private def fixedVecs (M : Subgroup SL(6, ZMod 2)) : Set (Fin 6 → ZMod 2) :=
  {w | ∀ m ∈ M, (m : SL(6, ZMod 2)) • w = w}

private theorem fixedVecs_add {M : Subgroup SL(6, ZMod 2)} {w₁ w₂ : Fin 6 → ZMod 2}
    (h₁ : w₁ ∈ fixedVecs M) (h₂ : w₂ ∈ fixedVecs M) : w₁ + w₂ ∈ fixedVecs M := by
  intro m hm
  rw [smul_add, h₁ m hm, h₂ m hm]

private theorem fixedVecs_smul {M : Subgroup SL(6, ZMod 2)} {y : SL(6, ZMod 2)}
    (hy : y ∈ Subgroup.normalizer (M : Set (SL(6, ZMod 2)))) {w : Fin 6 → ZMod 2}
    (hw : w ∈ fixedVecs M) : y • w ∈ fixedVecs M := by
  intro n hn
  have hy' : y⁻¹ ∈ Subgroup.normalizer (M : Set (SL(6, ZMod 2))) := Subgroup.inv_mem _ hy
  have hmem : y⁻¹ * n * y ∈ M := by
    have h := (Subgroup.mem_normalizer_iff.mp hy' n).mp hn
    simpa using h
  calc n • (y • w) = (n * y) • w := (mul_smul n y w).symm
    _ = (y * (y⁻¹ * n * y)) • w := by rw [show n * y = y * (y⁻¹ * n * y) by group]
    _ = y • ((y⁻¹ * n * y) • w) := mul_smul y _ w
    _ = y • w := by rw [hw _ hmem]

private theorem exists_ne_zero_fixedVecs (M : Subgroup SL(6, ZMod 2)) (hM : IsPGroup 2 M) :
    ∃ w : Fin 6 → ZMod 2, w ≠ 0 ∧ w ∈ fixedVecs M := by
  let : DistribMulAction ↥M (Fin 6 → ZMod 2) := DistribMulAction.compHom _ M.subtype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (Fin 6 → ZMod 2) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  obtain ⟨w, hw, hw0⟩ := hM.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin 6 → ZMod 2) h2 (a := 0) (by simp [MulAction.mem_fixedPoints])
  refine ⟨w, ?_, ?_⟩
  · intro h
    exact hw0 h.symm
  · intro m hm
    have := (MulAction.mem_fixedPoints.mp hw) ⟨m, hm⟩
    simpa using this

private theorem eq_bot_of_transvection_normalized (M : Subgroup SL(6, ZMod 2))
    (hM : IsPGroup 2 M)
    (hnorm : ∀ (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0),
      transElem6 c hc ∈ Subgroup.normalizer (M : Set (SL(6, ZMod 2)))) : M = ⊥ := by
  obtain ⟨w, hwne, hw⟩ := exists_ne_zero_fixedVecs M hM
  have hiso : ∀ c : Fin 6 → ZMod 2, c ⬝ᵥ (A6 *ᵥ c) = 0 := by decide +kernel
  have hAw : A6 *ᵥ w ≠ 0 := by
    intro h
    apply hwne
    have h' : A6 *ᵥ (A6 *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, A6_mul_self, Matrix.one_mulVec]
    rw [h, Matrix.mulVec_zero] at h'
    exact h'.symm
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hAw
  have hk1 : (A6 *ᵥ w) k = 1 := by
    have hz : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact hz _ hk
  have hmem : ∀ (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0),
      c ⬝ᵥ (A6 *ᵥ w) = 1 → c ∈ fixedVecs M := by
    intro c hc hcw
    have hmem := fixedVecs_smul (hnorm c hc) hw
    have hstep : (transElem6 c hc : SL(6, ZMod 2)) • w = w + c := by
      rw [transElem6_smul, hcw, one_smul]
    rw [hstep] at hmem
    have hsum : (w + c) + w ∈ fixedVecs M := fixedVecs_add hmem hw
    have hw2 : (w + c) + w = c := by
      ext i
      simp only [Pi.add_apply]
      rw [add_comm (w i) (c i), add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hw2] at hsum
    exact hsum
  have hsingle : ∀ j : Fin 6, Pi.single j 1 ∈ fixedVecs M := by
    intro j
    have hcj : (Pi.single j 1) ⬝ᵥ (A6 *ᵥ w) = 0 ∨
        (Pi.single j 1) ⬝ᵥ (A6 *ᵥ w) = 1 := by
      have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      exact h _
    rcases hcj with h0 | h1
    · have hk_mem : Pi.single k 1 ∈ fixedVecs M := by
        apply hmem
        · exact hiso _
        · rw [single_one_dotProduct]; exact hk1
      have hsum_iso : (Pi.single k 1 + Pi.single j 1) ⬝ᵥ
          (A6 *ᵥ (Pi.single k 1 + Pi.single j 1)) = 0 := hiso _
      have hsum_beta : (Pi.single k 1 + Pi.single j 1) ⬝ᵥ (A6 *ᵥ w) = 1 := by
        rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct, hk1]
        have h0' : (A6 *ᵥ w) j = 0 := by
          simpa [single_one_dotProduct] using h0
        rw [h0', add_zero]
      have hsum_mem : Pi.single k 1 + Pi.single j 1 ∈ fixedVecs M :=
        hmem _ hsum_iso hsum_beta
      have hdiff : (Pi.single j (1 : ZMod 2) : Fin 6 → ZMod 2) =
          ((Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) +
            (Pi.single j (1 : ZMod 2) : Fin 6 → ZMod 2)) +
              (Pi.single k (1 : ZMod 2) : Fin 6 → ZMod 2) := by
        ext i
        by_cases hk : i = k <;> by_cases hj : i = j <;> by_cases hkj : k = j <;>
          simp [Pi.add_apply, hk, hj, hkj, CharTwo.add_self_eq_zero]
      rw [hdiff]
      exact fixedVecs_add hsum_mem hk_mem
    · exact hmem _ (hiso _) h1
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  have hmat : (m : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    ext i j
    have hmv : ((m : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        Pi.single j 1 = Pi.single j 1 := by
      ext a
      have h := congrArg (fun v : Fin 6 → ZMod 2 => v a) (hsingle j m hm)
      simpa [Matrix.SpecialLinearGroup.smul_def] using h
    rw [Matrix.mulVec_single_one] at hmv
    have hcol := congrFun hmv i
    simpa [Matrix.col_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using hcol
  exact Subtype.ext (by rw [hmat, Matrix.SpecialLinearGroup.coe_one])

private def G7 : Matrix (Fin 6 ⊕ Fin 1) (Fin 6 ⊕ Fin 1) (ZMod 2) := fromBlocks A6 0 0 1

private theorem A6_alt : ∀ v : Fin 6 → ZMod 2, v ⬝ᵥ (A6 *ᵥ v) = 0 := by
  decide +kernel

private theorem qA6q_transpose_eq_zero (q : Matrix (Fin 1) (Fin 6) (ZMod 2)) :
    q * A6 * qᵀ = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  have hrow : (q * A6).row 0 = A6 *ᵥ q.row 0 := by
    rw [← Matrix.vecMul_transpose, A6_transpose]
    rfl
  have hcol : qᵀ.col 0 = q.row 0 := by
    funext i
    simp [Matrix.col, Matrix.row, Matrix.transpose_apply]
  rw [Matrix.mul_apply]
  change (q * A6).row 0 ⬝ᵥ qᵀ.col 0 = 0
  rw [hrow, hcol, dotProduct_comm]
  exact A6_alt _

private theorem bilin_isometry {ι : Type*} [Fintype ι]
    {G Z : Matrix ι ι (ZMod 2)} (hZ : Zᵀ * G * Z = G) (u v : ι → ZMod 2) :
    (Z *ᵥ u) ⬝ᵥ (G *ᵥ (Z *ᵥ v)) = u ⬝ᵥ (G *ᵥ v) := by
  calc (Z *ᵥ u) ⬝ᵥ (G *ᵥ (Z *ᵥ v))
      = ((Z *ᵥ u) ᵥ* G) ⬝ᵥ (Z *ᵥ v) := Matrix.dotProduct_mulVec _ G _
    _ = (((Z *ᵥ u) ᵥ* G) ᵥ* Z) ⬝ᵥ v := Matrix.dotProduct_mulVec _ Z v
    _ = (u ᵥ* (Zᵀ * G * Z)) ⬝ᵥ v := by
          rw [← Matrix.vecMul_transpose Z u, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
            Matrix.mul_assoc]
    _ = (u ᵥ* G) ⬝ᵥ v := by rw [hZ]
    _ = u ⬝ᵥ (G *ᵥ v) := (Matrix.dotProduct_mulVec u G v).symm

private theorem p_eq_zero_of_isometry
    (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) (p : Matrix (Fin 6) (Fin 1) (ZMod 2))
    (q : Matrix (Fin 1) (Fin 6) (ZMod 2)) (r : Matrix (Fin 1) (Fin 1) (ZMod 2))
    (h : fromBlocks P p q r * G7 * (fromBlocks P p q r)ᵀ = G7) : p = 0 := by
  have hZ : ((fromBlocks P p q r)ᵀ)ᵀ * G7 * (fromBlocks P p q r)ᵀ = G7 := by
    rw [Matrix.transpose_transpose]
    exact h
  have hpv : ∀ v : Fin 6 → ZMod 2, (pᵀ *ᵥ v) 0 = 0 := by
    intro v
    let v' : Fin 6 ⊕ Fin 1 → ZMod 2 := Sum.elim v 0
    have hb := bilin_isometry hZ v' v'
    have hZv : (fromBlocks P p q r)ᵀ *ᵥ v' = Sum.elim (Pᵀ *ᵥ v) (pᵀ *ᵥ v) := by
      rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_mulVec]
      simp [v', Matrix.mulVec_zero]
    have hGv : G7 *ᵥ (Sum.elim (Pᵀ *ᵥ v) (pᵀ *ᵥ v)) =
        Sum.elim (A6 *ᵥ (Pᵀ *ᵥ v)) (pᵀ *ᵥ v) := by
      simp only [G7]
      rw [Matrix.fromBlocks_mulVec]
      simp [Matrix.zero_mulVec]
    have hL : ((fromBlocks P p q r)ᵀ *ᵥ v') ⬝ᵥ
        (G7 *ᵥ ((fromBlocks P p q r)ᵀ *ᵥ v')) =
        (Pᵀ *ᵥ v) ⬝ᵥ (A6 *ᵥ (Pᵀ *ᵥ v)) +
          ((pᵀ *ᵥ v) 0) * ((pᵀ *ᵥ v) 0) := by
      rw [hZv, hGv, sumElim_dotProduct_sumElim]
      simp [dotProduct]
    have hGv' : G7 *ᵥ v' = Sum.elim (A6 *ᵥ v) 0 := by
      simp only [G7]
      rw [Matrix.fromBlocks_mulVec]
      simp [v', Matrix.mulVec_zero]
    have hR : v' ⬝ᵥ (G7 *ᵥ v') = 0 := by
      rw [hGv', sumElim_dotProduct_sumElim]
      simp [A6_alt]
    rw [hL, hR, A6_alt] at hb
    have hsq : ((pᵀ *ᵥ v) 0) * ((pᵀ *ᵥ v) 0) = 0 := by simpa using hb
    have hz : ∀ x : ZMod 2, x * x = 0 → x = 0 := by decide
    exact hz _ hsq
  ext i j
  fin_cases j
  have h := hpv (Pi.single i 1)
  simpa [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Pi.single_apply,
    Fin.sum_univ_one] using h

private theorem block_form_A7 {Y : Matrix (Fin 7) (Fin 7) (ZMod 2)}
    (hY : Y * A7 * Yᵀ = A7) :
    ∃ P : Matrix (Fin 6) (Fin 6) (ZMod 2),
      bl e7 Y = fromBlocks P 0 0 1 ∧ P * A6 * Pᵀ = A6 := by
  have hYb : bl e7 Y * G7 * (bl e7 Y)ᵀ = G7 := by
    have h := congrArg (bl e7) hY
    rw [bl_mul, bl_mul, bl_transpose, bl_e7_A7] at h
    simpa only [G7] using h
  obtain ⟨P, p, q, r, hYeq⟩ : ∃ P p q r, bl e7 Y = fromBlocks P p q r :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks _).symm⟩
  have h : fromBlocks P p q r * G7 * (fromBlocks P p q r)ᵀ = G7 := by rwa [hYeq] at hYb
  have hYG : fromBlocks P p q r * G7 = fromBlocks (P * A6) p (q * A6) r := by
    simp only [G7, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_one]
  have hblocks : fromBlocks (P * A6 * Pᵀ + p * pᵀ) (P * A6 * qᵀ + p * rᵀ)
      (q * A6 * Pᵀ + r * pᵀ) (q * A6 * qᵀ + r * rᵀ) = G7 := by
    rw [← h, hYG, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  obtain ⟨h11, h12, h21, h22⟩ := Matrix.fromBlocks_inj.mp hblocks
  have hp : p = 0 := p_eq_zero_of_isometry P p q r h
  have hr : r = 1 := by
    have hq0 : q * A6 * qᵀ = 0 := qA6q_transpose_eq_zero q
    have hr2 : r * rᵀ = 1 := by
      rw [hq0, zero_add] at h22
      exact h22
    ext i j
    fin_cases i
    fin_cases j
    have h : r 0 0 * r 0 0 = 1 := by
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one] using
        congrArg (fun M => M 0 0) hr2
    have hz : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide
    simpa using hz (r 0 0) h
  have h11' : P * A6 * Pᵀ = A6 := by
    rw [hp] at h11
    simpa using h11
  have hdetP : P.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det h11'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, A6_det, mul_one] at h
    rw [h0] at h
    norm_num at h
  have hPinvT : Pᵀ * (Pᵀ)⁻¹ = 1 := by
    rw [Matrix.mul_nonsing_inv]
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hdetP
  have hA6inv : A6 * A6 = 1 := A6_mul_self
  have hq : q = 0 := by
    have h3 : q * A6 * Pᵀ = 0 := by
      rw [hp] at h21
      simpa using h21
    have h3' : q * A6 = 0 := by
      calc q * A6 = q * A6 * (Pᵀ * (Pᵀ)⁻¹) := by
            rw [hPinvT, Matrix.mul_one]
        _ = (q * A6 * Pᵀ) * (Pᵀ)⁻¹ := by rw [← Matrix.mul_assoc]
        _ = 0 := by rw [h3]; simp
    calc q = q * (A6 * A6) := by rw [hA6inv, Matrix.mul_one]
      _ = (q * A6) * A6 := by rw [← Matrix.mul_assoc]
      _ = 0 := by rw [h3']; simp
  exact ⟨P, by rw [hYeq, hp, hq, hr], h11'⟩

private def BD6 (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    Matrix (Fin 6 ⊕ Fin 1) (Fin 6 ⊕ Fin 1) (ZMod 2) := fromBlocks P 0 0 1

private theorem BD6_mul (P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    BD6 P * BD6 Q = BD6 (P * Q) := by
  simp only [BD6, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one]

private theorem BD6_one : BD6 (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [BD6, Matrix.fromBlocks, Matrix.one_apply]

private theorem BD6_inj {P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : BD6 P = BD6 Q) :
    P = Q :=
  (Matrix.fromBlocks_inj.mp h).1

private theorem BD6_mul_inv (P : SL(6, ZMod 2)) :
    BD6 (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      BD6 ((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
  rw [BD6_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, BD6_one]

private theorem inv_T0_SL7 : ((W7.T 0)⁻¹ : SL(7, ZMod 2)) = W7.T 0 ^ 2 :=
  inv_eq_pow_two_of_cube (x := W7.T 0) (W7.pow_T 0)

private theorem inv_T1_SL7 : ((W7.T 1)⁻¹ : SL(7, ZMod 2)) = W7.T 1 ^ 2 :=
  inv_eq_pow_two_of_cube (x := W7.T 1) (W7.pow_T 1)

private theorem inv_T2_SL7 : ((W7.T 2)⁻¹ : SL(7, ZMod 2)) = W7.T 2 ^ 2 :=
  inv_eq_pow_two_of_cube (x := W7.T 2) (W7.pow_T 2)

private theorem t1M7_sq_transpose : (W7.t1M ^ 2)ᵀ = W7.t1Mi := by decide +kernel

private theorem t2M7_sq_transpose : (W7.t2M ^ 2)ᵀ = W7.t2Mi := by decide +kernel

private theorem t3M7_sq_transpose : (W7.t3M ^ 2)ᵀ = W7.t3Mi := by decide +kernel

private theorem det_eq_one_of_form (P : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (h : P * A6 * Pᵀ = A6) : P.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, A6_det, mul_one] at hd
  have hz : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide
  exact hz _ hd

private def blockSubgroup (N : Subgroup SL(7, ZMod 2)) : Subgroup SL(6, ZMod 2) where
  carrier := {P | ∃ n : ↥N, bl e7 (n : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
    BD6 (P : Matrix (Fin 6) (Fin 6) (ZMod 2))}
  one_mem' := by
    refine ⟨1, ?_⟩
    rw [Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_one,
      bl_one, BD6_one]
  mul_mem' := by
    rintro P Q ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n * m, ?_⟩
    rw [show (((n * m : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        ((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          ((m : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) by
      rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]]
    rw [bl_mul, hn, hm]
    rw [show ((P * Q : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (Q : Matrix (Fin 6) (Fin 6) (ZMod 2)) by
      rw [Matrix.SpecialLinearGroup.coe_mul]]
    rw [BD6_mul]
  inv_mem' := by
    rintro P ⟨n, hn⟩
    refine ⟨n⁻¹, ?_⟩
    have h1 : BD6 ((P : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
        BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) = 1 :=
      BD6_mul_inv P
    have h2 : BD6 ((P : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
        bl e7 (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 1 := by
      have hnn : ((n * n⁻¹ : ↥N) : SL(7, ZMod 2)) = 1 := by
        rw [mul_inv_cancel]
        rfl
      have h := congrArg (fun z : SL(7, ZMod 2) =>
        bl e7 (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hnn
      rw [show (((n * n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
          ((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
            (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) by
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]] at h
      rw [bl_mul, hn, Matrix.SpecialLinearGroup.coe_one, bl_one] at h
      exact h
    have h4 : BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
        BD6 ((P : Matrix (Fin 6) (Fin 6) (ZMod 2))) = 1 := by
      simpa using BD6_mul_inv (P⁻¹)
    have h3 : bl e7 (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) := by
      calc bl e7 (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))
          = 1 * bl e7 (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) :=
              (Matrix.one_mul _).symm
        _ = (BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
              BD6 ((P : Matrix (Fin 6) (Fin 6) (ZMod 2)))) *
                bl e7 (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
              rw [h4]
        _ = BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
              (BD6 ((P : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
                bl e7 (((n⁻¹ : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) := by
              rw [Matrix.mul_assoc]
        _ = BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) * 1 := by
              rw [h2]
        _ = BD6 (((P⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) :=
              Matrix.mul_one _
    exact h3

private def transElem7 (c : Fin 7 → ZMod 2) (hc : c ⬝ᵥ (A7 *ᵥ c) = 0) : SL(7, ZMod 2) :=
  ⟨tmat A7 c, detOne_of_mul_eq_one (tmat_mul_self A7 c hc)⟩

private theorem coe_transElem7 (c : Fin 7 → ZMod 2) (hc : c ⬝ᵥ (A7 *ᵥ c) = 0) :
    ((transElem7 c hc : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = tmat A7 c := rfl

private theorem transElem7_mul_self (c : Fin 7 → ZMod 2) (hc : c ⬝ᵥ (A7 *ᵥ c) = 0) :
    transElem7 c hc * transElem7 c hc = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_transElem7,
    tmat_mul_self A7 c hc]

private theorem transElem7_fixed {σ : MulAut SL(7, ZMod 2)} {g : SL(7, ZMod 2)}
    (hσ : σ = MulAut.conj g * slGraphAut 7 (ZMod 2))
    (hG : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) = A7)
    (c : Fin 7 → ZMod 2) (hc : c ⬝ᵥ (A7 *ᵥ c) = 0) :
    σ (transElem7 c hc) = transElem7 c hc := by
  rw [hσ, MulAut.mul_apply]
  apply fixed_of_matrix_eq
  · rw [hG]; exact A7_transpose
  · rw [coe_transElem7, hG]
    exact tmat_isometry A7 A7_mul_self A7_transpose c hc

private theorem bl_e7_tmat (c : Fin 6 → ZMod 2) :
    bl e7 (tmat A7 (fun i => Sum.elim c 0 (e7 i))) = BD6 (tmat A6 c) := by
  revert c
  decide +kernel

private theorem c7_isotropic :
    ∀ c : Fin 6 → ZMod 2, c ⬝ᵥ (A6 *ᵥ c) = 0 →
      (fun i => Sum.elim c 0 (e7 i)) ⬝ᵥ
        (A7 *ᵥ (fun i => Sum.elim c 0 (e7 i))) = 0 := by
  decide +kernel

private theorem p_eq_zero_of_fixed_t (p : Matrix (Fin 6) (Fin 1) (ZMod 2))
    (h0 : p = W6.t1M * p) (h1 : p = W6.t2M * p) (h2 : p = W6.t3M * p) : p = 0 := by
  revert p
  decide +kernel

private theorem eq_A7_of_fixed {g : SL(7, ZMod 2)}
    (hGsym : (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ = g)
    (h0 : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t1Mi =
      W7.t1M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2)))
    (h1 : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t2Mi =
      W7.t2M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2)))
    (h2 : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t3Mi =
      W7.t3M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2))) :
    (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) = A7 := by
  have hsym_bl : (bl e7 (g : Matrix (Fin 7) (Fin 7) (ZMod 2)))ᵀ =
      bl e7 (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [← bl_transpose, hGsym]
  obtain ⟨P, p, q, r, hYeq⟩ : ∃ P p q r,
      bl e7 (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) = fromBlocks P p q r :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks _).symm⟩
  rw [hYeq, Matrix.fromBlocks_transpose] at hsym_bl
  obtain ⟨hPsym, hqp, hpq, hrsym⟩ := Matrix.fromBlocks_inj.mp hsym_bl
  have hrel0 : bl e7 ((g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t1Mi) =
      bl e7 (W7.t1M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2))) := by rw [h0]
  rw [bl_mul, bl_mul, hYeq, bl_e7_t1Mi, bl_e7_t1M] at hrel0
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hrel0
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one] at hrel0
  have hP0 : P * W6.t1Mi = W6.t1M * P := (Matrix.fromBlocks_inj.mp hrel0).1
  have hp0 : p = W6.t1M * p := (Matrix.fromBlocks_inj.mp hrel0).2.1
  have hrel1 : bl e7 ((g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t2Mi) =
      bl e7 (W7.t2M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2))) := by rw [h1]
  rw [bl_mul, bl_mul, hYeq, bl_e7_t2Mi, bl_e7_t2M] at hrel1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hrel1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one] at hrel1
  have hP1 : P * W6.t2Mi = W6.t2M * P := (Matrix.fromBlocks_inj.mp hrel1).1
  have hp1 : p = W6.t2M * p := (Matrix.fromBlocks_inj.mp hrel1).2.1
  have hrel2 : bl e7 ((g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t3Mi) =
      bl e7 (W7.t3M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2))) := by rw [h2]
  rw [bl_mul, bl_mul, hYeq, bl_e7_t3Mi, bl_e7_t3M] at hrel2
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hrel2
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one] at hrel2
  have hP2 : P * W6.t3Mi = W6.t3M * P := (Matrix.fromBlocks_inj.mp hrel2).1
  have hp2 : p = W6.t3M * p := (Matrix.fromBlocks_inj.mp hrel2).2.1
  have hp : p = 0 := p_eq_zero_of_fixed_t p hp0 hp1 hp2
  have hq : q = 0 := by
    rw [hp, Matrix.transpose_eq_zero] at hqp
    exact hqp
  have hdetprod : P.det * r.det = 1 := by
    have hdetbl : (bl e7 (g : Matrix (Fin 7) (Fin 7) (ZMod 2))).det =
        (g : Matrix (Fin 7) (Fin 7) (ZMod 2)).det :=
      Matrix.det_submatrix_equiv_self e7.symm (g : Matrix (Fin 7) (Fin 7) (ZMod 2))
    have h := hdetbl
    rw [hYeq, hp, hq, Matrix.det_fromBlocks_zero₁₂] at h
    rw [Matrix.SpecialLinearGroup.det_coe] at h
    exact h
  have hPdet : P.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetprod
    exact zero_ne_one hdetprod
  have hP : P = A6 := eq_A6 hPsym hPdet hP0 hP1 hP2
  have hr : r = 1 := by
    have hrdet : r.det = 1 := by
      rw [hP, A6_det, one_mul] at hdetprod
      exact hdetprod
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_fin_one] using hrdet
  have hfinal : bl e7 (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) = fromBlocks A6 0 0 1 := by
    rw [hYeq, hP, hp, hq, hr]
  exact bl_injective e7 (by rw [hfinal, bl_e7_A7])

theorem o2_SL6_of_cen
    (hcen : ∀ k : SL(6, ZMod 2), (∀ i, k * W6.T i = W6.T i * k) → ∃ v, k = vecElt W6.T v) :
    ∀ σ : MulAut SL(6, ZMod 2), σ * σ = 1 → (∀ i, σ (W6.T i) = W6.T i) →
      ∀ N : Subgroup SL(6, ZMod 2), IsPGroup 2 N → (∀ n ∈ N, σ n = n) →
        (∀ c : SL(6, ZMod 2), σ c = c → ∀ n ∈ N, c * n * c⁻¹ ∈ N) → N = ⊥ := by
  intro σ hσ2 hfixT N hP hfixN hnorm
  obtain ⟨g, ε, hε, hσ⟩ := aut_sl_zmod_two (n := 6) (by norm_num) σ
  interval_cases ε
  ·
    have hσc : σ = MulAut.conj g := by rw [hσ, pow_zero, mul_one]
    have hgcomm : ∀ i, g * W6.T i = W6.T i * g := by
      intro i
      have h := hfixT i
      rw [hσc, MulAut.conj_apply] at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    obtain ⟨v, hv⟩ := hcen g hgcomm
    have hg3 : g ^ 3 = 1 := by
      rw [hv]
      exact vecElt_pow_three W6.wreathFacts v
    have hg2comm : ∀ y : SL(6, ZMod 2), (g * g) * y = y * (g * g) := by
      intro y
      have h := hσ2
      rw [hσc, ← map_mul] at h
      have hy := congrArg (fun f : MulAut SL(6, ZMod 2) => f y) h
      rw [MulAut.conj_apply, MulAut.one_apply] at hy
      exact (mul_inv_eq_iff_eq_mul).mp hy
    have hg2 : g * g = 1 := by
      have : IsSimpleGroup SL(6, ZMod 2) := isSimpleGroup_SL_zmod_two (n := 6) (by norm_num)
      apply eq_one_of_mem_center (center_eq_bot_of_simple not_comm_SL6)
      exact Subgroup.mem_center_iff.mpr (fun y => (hg2comm y).symm)
    have hg1 : g = 1 := by
      have h3 : g ^ 2 * g = 1 := by
        rw [← pow_succ, hg3]
      rw [pow_two, hg2, one_mul] at h3
      exact h3
    have hσ1 : σ = 1 := by rw [hσc, hg1, map_one]
    have hNnorm : N.Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn c
      exact hnorm c (by rw [hσ1, MulAut.one_apply]) n hn
    have : IsSimpleGroup SL(6, ZMod 2) := isSimpleGroup_SL_zmod_two (n := 6) (by norm_num)
    have : N.Normal := hNnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hmem : W6.T 0 ∈ N := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := hP (⟨W6.T 0, hmem⟩ : N)
      have hord : orderOf (⟨W6.T 0, hmem⟩ : N) = 3 := by
        rw [Subgroup.orderOf_mk, orderOf_T0_SL6]
      have hdvd : 3 ∣ 2 ^ k := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one hk
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  ·
    have hσ1 : σ = MulAut.conj g * slGraphAut 6 (ZMod 2) := by rw [hσ, pow_one]
    have hδinv : (slGraphAut 6 (ZMod 2))⁻¹ = slGraphAut 6 (ZMod 2) := slGraphAut_inv 6
    have hstep : (MulAut.conj g * slGraphAut 6 (ZMod 2)) *
        (MulAut.conj g * slGraphAut 6 (ZMod 2)) =
        MulAut.conj g * (slGraphAut 6 (ZMod 2) * MulAut.conj g *
          slGraphAut 6 (ZMod 2)) := by group
    have hconj : slGraphAut 6 (ZMod 2) * MulAut.conj g * (slGraphAut 6 (ZMod 2))⁻¹ =
        MulAut.conj (slGraphAut 6 (ZMod 2) g) := conj_mulAut_conj _ g
    rw [hδinv] at hconj
    have hσ2conj : MulAut.conj (g * slGraphAut 6 (ZMod 2) g) = 1 := by
      have h := hσ2
      rw [hσ1, hstep, hconj] at h
      rwa [← map_mul] at h
    have hgδcomm : ∀ y : SL(6, ZMod 2), (g * slGraphAut 6 (ZMod 2) g) * y =
        y * (g * slGraphAut 6 (ZMod 2) g) := by
      intro y
      have h := congrArg (fun f : MulAut SL(6, ZMod 2) => f y) hσ2conj
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    have : IsSimpleGroup SL(6, ZMod 2) := isSimpleGroup_SL_zmod_two (n := 6) (by norm_num)
    have hgδ1 : g * slGraphAut 6 (ZMod 2) g = 1 := by
      apply eq_one_of_mem_center (center_eq_bot_of_simple not_comm_SL6)
      exact Subgroup.mem_center_iff.mpr (fun y => (hgδcomm y).symm)
    have hGG' : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        (((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hG'G : (((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hDmat : ((slGraphAut 6 (ZMod 2) g : SL(6, ZMod 2)) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        (((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))ᵀ := by
      rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
    have h1 : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
        (((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))ᵀ = 1 := by
      have h := congrArg (fun z : SL(6, ZMod 2) =>
        (z : Matrix (Fin 6) (Fin 6) (ZMod 2))) hgδ1
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
      rwa [hDmat] at h
    have h2 : (((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ = 1 := by
      have h := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
    have hGsym : (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ =
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      calc (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ =
          1 * (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ := (Matrix.one_mul _).symm
        _ = ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
              (((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))) *
              (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ := by rw [hGG']
        _ = (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
              ((((g⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
                (g : Matrix (Fin 6) (Fin 6) (ZMod 2))ᵀ) := by rw [Matrix.mul_assoc]
        _ = (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * 1 := by rw [h2]
        _ = (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := Matrix.mul_one _
    have hinv0 : ((((W6.T 0)⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))ᵀ =
        W6.t1Mi := by
      rw [inv_T0_SL6, Matrix.SpecialLinearGroup.coe_pow, W6.coe_T]
      exact t1M_sq_transpose
    have hinv1 : ((((W6.T 1)⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))ᵀ =
        W6.t2Mi := by
      rw [inv_T1_SL6, Matrix.SpecialLinearGroup.coe_pow, W6.coe_T]
      exact t2M_sq_transpose
    have hinv2 : ((((W6.T 2)⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)))ᵀ =
        W6.t3Mi := by
      rw [inv_T2_SL6, Matrix.SpecialLinearGroup.coe_pow, W6.coe_T]
      exact t3M_sq_transpose
    have hfixT' : ∀ i, MulAut.conj g (slGraphAut 6 (ZMod 2) (W6.T i)) = W6.T i := by
      intro i
      have h := hfixT i
      rwa [hσ1, MulAut.mul_apply] at h
    have h0 : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * W6.t1Mi =
        W6.t1M * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      have h := mul_transpose_eq_of_fixed (hfixT' 0)
      rwa [hinv0, W6.coe_T] at h
    have h1' : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * W6.t2Mi =
        W6.t2M * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      have h := mul_transpose_eq_of_fixed (hfixT' 1)
      rwa [hinv1, W6.coe_T] at h
    have h2' : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * W6.t3Mi =
        W6.t3M * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      have h := mul_transpose_eq_of_fixed (hfixT' 2)
      rwa [hinv2, W6.coe_T] at h
    have hdet : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).det ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.det_coe]
      exact one_ne_zero
    have hG : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = A6 :=
      eq_A6 hGsym hdet h0 h1' h2'
    have hnorm' : ∀ (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0),
        transElem6 c hc ∈ Subgroup.normalizer (N : Set (SL(6, ZMod 2))) := by
      intro c hc
      exact mem_normalizer_of_conj_le (transElem6_mul_self c hc)
        (fun n hn => hnorm (transElem6 c hc) (transElem6_fixed hσ1 hG c hc) n hn)
    exact eq_bot_of_transvection_normalized N hP hnorm'

theorem o2_SL7_of_cen
    (hcen : ∀ k : SL(7, ZMod 2), (∀ i, k * W7.T i = W7.T i * k) → ∃ v, k = vecElt W7.T v) :
    ∀ σ : MulAut SL(7, ZMod 2), σ * σ = 1 → (∀ i, σ (W7.T i) = W7.T i) →
      ∀ N : Subgroup SL(7, ZMod 2), IsPGroup 2 N → (∀ n ∈ N, σ n = n) →
        (∀ c : SL(7, ZMod 2), σ c = c → ∀ n ∈ N, c * n * c⁻¹ ∈ N) → N = ⊥ := by
  intro σ hσ2 hfixT N hP hfixN hnorm
  obtain ⟨g, ε, hε, hσ⟩ := aut_sl_zmod_two (n := 7) (by norm_num) σ
  interval_cases ε
  ·
    have hσc : σ = MulAut.conj g := by rw [hσ, pow_zero, mul_one]
    have hgcomm : ∀ i, g * W7.T i = W7.T i * g := by
      intro i
      have h := hfixT i
      rw [hσc, MulAut.conj_apply] at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    obtain ⟨v, hv⟩ := hcen g hgcomm
    have hg3 : g ^ 3 = 1 := by
      rw [hv]
      exact vecElt_pow_three W7.wreathFacts v
    have hg2comm : ∀ y : SL(7, ZMod 2), (g * g) * y = y * (g * g) := by
      intro y
      have h := hσ2
      rw [hσc, ← map_mul] at h
      have hy := congrArg (fun f : MulAut SL(7, ZMod 2) => f y) h
      rw [MulAut.conj_apply, MulAut.one_apply] at hy
      exact (mul_inv_eq_iff_eq_mul).mp hy
    have hg2 : g * g = 1 := by
      have : IsSimpleGroup SL(7, ZMod 2) := isSimpleGroup_SL_zmod_two (n := 7) (by norm_num)
      apply eq_one_of_mem_center (center_eq_bot_of_simple not_comm_SL7)
      exact Subgroup.mem_center_iff.mpr (fun y => (hg2comm y).symm)
    have hg1 : g = 1 := by
      have h3 : g ^ 2 * g = 1 := by
        rw [← pow_succ, hg3]
      rw [pow_two, hg2, one_mul] at h3
      exact h3
    have hσ1 : σ = 1 := by rw [hσc, hg1, map_one]
    have hNnorm : N.Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn c
      exact hnorm c (by rw [hσ1, MulAut.one_apply]) n hn
    have : IsSimpleGroup SL(7, ZMod 2) := isSimpleGroup_SL_zmod_two (n := 7) (by norm_num)
    have : N.Normal := hNnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      have hmem : W7.T 0 ∈ N := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := hP (⟨W7.T 0, hmem⟩ : N)
      have hord : orderOf (⟨W7.T 0, hmem⟩ : N) = 3 := by
        rw [Subgroup.orderOf_mk, orderOf_T0_SL7]
      have hdvd : 3 ∣ 2 ^ k := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one hk
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  ·
    have hσ1 : σ = MulAut.conj g * slGraphAut 7 (ZMod 2) := by rw [hσ, pow_one]
    have hδinv : (slGraphAut 7 (ZMod 2))⁻¹ = slGraphAut 7 (ZMod 2) := slGraphAut_inv 7
    have hstep : (MulAut.conj g * slGraphAut 7 (ZMod 2)) *
        (MulAut.conj g * slGraphAut 7 (ZMod 2)) =
        MulAut.conj g * (slGraphAut 7 (ZMod 2) * MulAut.conj g *
          slGraphAut 7 (ZMod 2)) := by group
    have hconj : slGraphAut 7 (ZMod 2) * MulAut.conj g * (slGraphAut 7 (ZMod 2))⁻¹ =
        MulAut.conj (slGraphAut 7 (ZMod 2) g) := conj_mulAut_conj _ g
    rw [hδinv] at hconj
    have hσ2conj : MulAut.conj (g * slGraphAut 7 (ZMod 2) g) = 1 := by
      have h := hσ2
      rw [hσ1, hstep, hconj] at h
      rwa [← map_mul] at h
    have hgδcomm : ∀ y : SL(7, ZMod 2), (g * slGraphAut 7 (ZMod 2) g) * y =
        y * (g * slGraphAut 7 (ZMod 2) g) := by
      intro y
      have h := congrArg (fun f : MulAut SL(7, ZMod 2) => f y) hσ2conj
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul).mp h
    have : IsSimpleGroup SL(7, ZMod 2) := isSimpleGroup_SL_zmod_two (n := 7) (by norm_num)
    have hgδ1 : g * slGraphAut 7 (ZMod 2) g = 1 := by
      apply eq_one_of_mem_center (center_eq_bot_of_simple not_comm_SL7)
      exact Subgroup.mem_center_iff.mpr (fun y => (hgδcomm y).symm)
    have hGG' : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        (((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hG'G : (((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) *
        (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hDmat : ((slGraphAut 7 (ZMod 2) g : SL(7, ZMod 2)) :
        Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        (((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)))ᵀ := by
      rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
    have h1 : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
        (((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)))ᵀ = 1 := by
      have h := congrArg (fun z : SL(7, ZMod 2) =>
        (z : Matrix (Fin 7) (Fin 7) (ZMod 2))) hgδ1
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
      rwa [hDmat] at h
    have h2 : (((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) *
        (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ = 1 := by
      have h := congrArg Matrix.transpose h1
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
    have hGsym : (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ =
        (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
      calc (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ =
          1 * (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ := (Matrix.one_mul _).symm
        _ = ((g : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
              (((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)))) *
              (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ := by rw [hGG']
        _ = (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
              ((((g⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) *
                (g : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ) := by rw [Matrix.mul_assoc]
        _ = (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * 1 := by rw [h2]
        _ = (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := Matrix.mul_one _
    have hinv0 : ((((W7.T 0)⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)))ᵀ =
        W7.t1Mi := by
      rw [inv_T0_SL7, Matrix.SpecialLinearGroup.coe_pow, W7.coe_T]
      exact t1M7_sq_transpose
    have hinv1 : ((((W7.T 1)⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)))ᵀ =
        W7.t2Mi := by
      rw [inv_T1_SL7, Matrix.SpecialLinearGroup.coe_pow, W7.coe_T]
      exact t2M7_sq_transpose
    have hinv2 : ((((W7.T 2)⁻¹ : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)))ᵀ =
        W7.t3Mi := by
      rw [inv_T2_SL7, Matrix.SpecialLinearGroup.coe_pow, W7.coe_T]
      exact t3M7_sq_transpose
    have hfixT' : ∀ i, MulAut.conj g (slGraphAut 7 (ZMod 2) (W7.T i)) = W7.T i := by
      intro i
      have h := hfixT i
      rwa [hσ1, MulAut.mul_apply] at h
    have h0 : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t1Mi =
        W7.t1M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
      have h := mul_transpose_eq_of_fixed (hfixT' 0)
      rwa [hinv0, W7.coe_T] at h
    have h1' : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t2Mi =
        W7.t2M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
      have h := mul_transpose_eq_of_fixed (hfixT' 1)
      rwa [hinv1, W7.coe_T] at h
    have h2' : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) * W7.t3Mi =
        W7.t3M * (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
      have h := mul_transpose_eq_of_fixed (hfixT' 2)
      rwa [hinv2, W7.coe_T] at h
    have hG : (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) = A7 :=
      eq_A7_of_fixed hGsym h0 h1' h2'
    have hmem_block : ∀ n ∈ N, ∃ P : Matrix (Fin 6) (Fin 6) (ZMod 2),
        bl e7 (((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) = BD6 P ∧
          P * A6 * Pᵀ = A6 := by
      intro n hn
      have hfix : σ n = n := hfixN n hn
      have hconj : MulAut.conj g (slGraphAut 7 (ZMod 2) n) = n := by
        have h := hfix
        rwa [hσ1, MulAut.mul_apply] at h
      have hmat : (n : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
          (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
            (n : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ =
          (g : Matrix (Fin 7) (Fin 7) (ZMod 2)) :=
        matrix_eq_of_fixed hconj
      have hY : (n : Matrix (Fin 7) (Fin 7) (ZMod 2)) * A7 *
          (n : Matrix (Fin 7) (Fin 7) (ZMod 2))ᵀ = A7 := by
        rw [hG] at hmat
        exact hmat
      obtain ⟨P, hPbl, hPform⟩ := block_form_A7 hY
      exact ⟨P, by simpa [BD6] using hPbl, hPform⟩
    let blockOf : ↥N → SL(6, ZMod 2) := fun n =>
      let h := hmem_block n n.2
      ⟨h.choose, det_eq_one_of_form h.choose h.choose_spec.2⟩
    have blockOf_spec : ∀ n : ↥N,
        bl e7 (((n : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
          BD6 ((blockOf n : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
      intro n
      change bl e7 (((n : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        BD6 (hmem_block n n.2).choose
      exact (hmem_block n n.2).choose_spec.1
    have blockOf_mul : ∀ n m : ↥N, blockOf (n * m) = blockOf n * blockOf m := by
      intro n m
      apply Subtype.ext
      apply BD6_inj
      rw [show ((blockOf n * blockOf m : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
          ((blockOf n : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
            ((blockOf m : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) by
        rw [Matrix.SpecialLinearGroup.coe_mul]]
      rw [← BD6_mul]
      rw [← blockOf_spec n, ← blockOf_spec m, ← blockOf_spec (n * m)]
      rw [show ((((n * m : ↥N) : SL(7, ZMod 2))) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
          ((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
            ((m : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) by
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]]
      rw [bl_mul]
    let f : ↥N →* blockSubgroup N :=
      MonoidHom.mk' (fun n => ⟨blockOf n, ⟨n, blockOf_spec n⟩⟩) (by
        intro n m
        apply Subtype.ext
        exact blockOf_mul n m)
    have hf_surj : Function.Surjective f := by
      intro P
      obtain ⟨n, hn⟩ := P.2
      change bl e7 (((n : ↥N) : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        BD6 ((P : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) at hn
      refine ⟨n, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply BD6_inj
      change BD6 ((blockOf n : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        BD6 ((P : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))
      rw [← blockOf_spec n, hn]
    have hN' : IsPGroup 2 (blockSubgroup N) :=
      IsPGroup.of_surjective hP f hf_surj
    have hnorm' : ∀ (c : Fin 6 → ZMod 2) (hc : c ⬝ᵥ (A6 *ᵥ c) = 0),
        transElem6 c hc ∈ Subgroup.normalizer
          ((blockSubgroup N : Subgroup SL(6, ZMod 2)) : Set (SL(6, ZMod 2))) := by
      intro c hc
      apply mem_normalizer_of_conj_le (transElem6_mul_self c hc)
      intro P hP
      obtain ⟨n, hn⟩ := hP
      let c7 : Fin 7 → ZMod 2 := fun i => Sum.elim c 0 (e7 i)
      have hc7 : c7 ⬝ᵥ (A7 *ᵥ c7) = 0 := c7_isotropic c hc
      let t7 : SL(7, ZMod 2) := transElem7 c7 hc7
      have ht7fix : σ t7 = t7 := transElem7_fixed hσ1 hG c7 hc7
      have hconj_mem : t7 * (n : SL(7, ZMod 2)) * t7⁻¹ ∈ N :=
        hnorm t7 ht7fix n n.2
      have ht7inv : t7⁻¹ = t7 := inv_eq_of_mul_eq_one_right (transElem7_mul_self c7 hc7)
      have ht6inv : (transElem6 c hc)⁻¹ = transElem6 c hc :=
        inv_eq_of_mul_eq_one_right (transElem6_mul_self c hc)
      have hblockconj : bl e7 ((((t7 * (n : SL(7, ZMod 2)) * t7⁻¹) : SL(7, ZMod 2)) :
          Matrix (Fin 7) (Fin 7) (ZMod 2))) =
          BD6 (((transElem6 c hc * P * (transElem6 c hc)⁻¹ : SL(6, ZMod 2)) :
            Matrix (Fin 6) (Fin 6) (ZMod 2))) := by
        rw [ht7inv, ht6inv]
        have ht7mat : (t7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) = tmat A7 c7 := by
          dsimp [t7]
          exact coe_transElem7 c7 hc7
        have ht6mat : ((transElem6 c hc : SL(6, ZMod 2)) :
            Matrix (Fin 6) (Fin 6) (ZMod 2)) = tmat A6 c := coe_transElem6 c hc
        have hR : (((transElem6 c hc * P * transElem6 c hc : SL(6, ZMod 2)) :
            Matrix (Fin 6) (Fin 6) (ZMod 2))) =
            tmat A6 c * (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) * tmat A6 c := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht6mat]
        calc bl e7 ((((t7 * (n : SL(7, ZMod 2)) * t7) : SL(7, ZMod 2)) :
              Matrix (Fin 7) (Fin 7) (ZMod 2)))
            = bl e7 ((t7 : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
                ((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
                  (t7 : Matrix (Fin 7) (Fin 7) (ZMod 2))) := by
                rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
          _ = bl e7 (tmat A7 c7 * ((n : SL(7, ZMod 2)) :
                Matrix (Fin 7) (Fin 7) (ZMod 2)) * tmat A7 c7) := by rw [ht7mat]
          _ = BD6 (tmat A6 c) * BD6 ((P : Matrix (Fin 6) (Fin 6) (ZMod 2))) *
                BD6 (tmat A6 c) := by
                rw [bl_mul, bl_mul, bl_e7_tmat, hn]
          _ = BD6 (tmat A6 c * (P : Matrix (Fin 6) (Fin 6) (ZMod 2)) * tmat A6 c) := by
                rw [BD6_mul, BD6_mul]
          _ = BD6 (((transElem6 c hc * P * transElem6 c hc : SL(6, ZMod 2)) :
                Matrix (Fin 6) (Fin 6) (ZMod 2))) := by rw [hR]
      exact ⟨⟨t7 * (n : SL(7, ZMod 2)) * t7⁻¹, hconj_mem⟩, hblockconj⟩
    have hbot : blockSubgroup N = ⊥ :=
      eq_bot_of_transvection_normalized (blockSubgroup N) hN' hnorm'
    rw [Subgroup.eq_bot_iff_forall]
    intro n hn
    have hmemN' : blockOf ⟨n, hn⟩ ∈ blockSubgroup N :=
      ⟨⟨n, hn⟩, blockOf_spec ⟨n, hn⟩⟩
    have hbotmem : blockOf ⟨n, hn⟩ ∈ (⊥ : Subgroup SL(6, ZMod 2)) := by
      rw [← hbot]
      exact hmemN'
    have hblockOf_one : blockOf ⟨n, hn⟩ = 1 := Subgroup.mem_bot.mp hbotmem
    have hbl1 : bl e7 (((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))) = 1 := by
      rw [blockOf_spec ⟨n, hn⟩, hblockOf_one, Matrix.SpecialLinearGroup.coe_one, BD6_one]
    have hmat : ((n : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 1 := by
      apply bl_injective e7
      rw [hbl1, bl_one]
    exact Subtype.ext (by rw [hmat, Matrix.SpecialLinearGroup.coe_one])

end CFSG.StandardType.GGFF

end
