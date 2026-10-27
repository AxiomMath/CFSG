module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.StandardType.QTwoSymplecticCav

open Matrix CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Chevalley (WSL coe_WSL)
open CFSG.SeitzReduction.SymplecticPilot (permSp mat_permSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap)
open scoped MatrixGroups commutatorElement

private def fourA : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fun i j => (!![0, 0, 0, 1; 0, 0, 1, 1; 1, 1, 0, 1; 1, 0, 1, 1] :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (finSumFinEquiv i) (finSumFinEquiv j)

private def fourB : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fun i j => (!![0, 0, 1, 1; 1, 1, 0, 0; 0, 1, 1, 1; 0, 0, 1, 0] :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (finSumFinEquiv i) (finSumFinEquiv j)

private def fourAInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fun i j => (!![0, 1, 0, 1; 1, 1, 1, 1; 1, 1, 0, 0; 1, 0, 0, 0] :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (finSumFinEquiv i) (finSumFinEquiv j)

private def fourBInv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fun i j => (!![1, 1, 1, 0; 1, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1] :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (finSumFinEquiv i) (finSumFinEquiv j)

@[expose] def binaryRotationMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fun i j => (!![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0] :
    Matrix (Fin 4) (Fin 4) (ZMod 2)) (finSumFinEquiv i) (finSumFinEquiv j)

private theorem fourA_symplectic : fourAᵀ * gram (ZMod 2) 2 * fourA = gram (ZMod 2) 2 := by
  decide +kernel

private theorem fourB_symplectic : fourBᵀ * gram (ZMod 2) 2 * fourB = gram (ZMod 2) 2 := by
  decide +kernel

private theorem fourA_inv : fourA * fourAInv = 1 := by decide +kernel
private theorem fourB_inv : fourB * fourBInv = 1 := by decide +kernel

private theorem four_commutator : fourA * fourB * fourAInv * fourBInv = binaryRotationMatrix := by
  decide +kernel

private theorem binaryRotationMatrix_four : binaryRotationMatrix ^ 4 = 1 := by decide +kernel
private theorem binaryRotationMatrix_sq_ne_one : binaryRotationMatrix ^ 2 ≠ 1 := by decide +kernel

theorem binaryRotationMatrix_symplectic :
    binaryRotationMatrixᵀ * gram (ZMod 2) 2 * binaryRotationMatrix = gram (ZMod 2) 2 := by
  decide +kernel

@[expose] noncomputable def binaryRotation : StatedSp 2 (ZMod 2) :=
  ofSymplecticMat binaryRotationMatrix binaryRotationMatrix_symplectic

private theorem mat_binaryRotation : mat 2 (ZMod 2) binaryRotation = binaryRotationMatrix := by
  rw [binaryRotation, mat_ofSymplecticMat]

theorem binaryRotation_mem_commutator : binaryRotation ∈ commutator (StatedSp 2 (ZMod 2)) := by
  let a := ofSymplecticMat fourA fourA_symplectic
  let b := ofSymplecticMat fourB fourB_symplectic
  have ha : mat 2 (ZMod 2) a = fourA := rfl
  have hb : mat 2 (ZMod 2) b = fourB := rfl
  have hai : mat 2 (ZMod 2) a⁻¹ = fourAInv := by
    calc mat 2 (ZMod 2) a⁻¹ = mat 2 (ZMod 2) a⁻¹ * (fourA * fourAInv) := by
            rw [fourA_inv, Matrix.mul_one]
      _ = (mat 2 (ZMod 2) a⁻¹ * mat 2 (ZMod 2) a) * fourAInv := by
            rw [ha, Matrix.mul_assoc]
      _ = fourAInv := by
            rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
  have hbi : mat 2 (ZMod 2) b⁻¹ = fourBInv := by
    calc mat 2 (ZMod 2) b⁻¹ = mat 2 (ZMod 2) b⁻¹ * (fourB * fourBInv) := by
            rw [fourB_inv, Matrix.mul_one]
      _ = (mat 2 (ZMod 2) b⁻¹ * mat 2 (ZMod 2) b) * fourBInv := by
            rw [hb, Matrix.mul_assoc]
      _ = fourBInv := by
            rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
  have hab : ⁅a, b⁆ = binaryRotation := by
    apply mat_injective
    rw [mat_binaryRotation, commutatorElement_def, map_mul, map_mul, map_mul, ha, hb, hai, hbi]
    exact four_commutator
  rw [← hab]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)

theorem binaryRotation_order : binaryRotation ^ 4 = 1 ∧ binaryRotation ^ 2 ≠ 1 := by
  constructor
  · apply mat_injective
    rw [map_pow, map_one, mat_binaryRotation]
    exact binaryRotationMatrix_four
  · intro h
    have h' := congrArg (mat 2 (ZMod 2)) h
    rw [map_pow, map_one, mat_binaryRotation] at h'
    exact binaryRotationMatrix_sq_ne_one h'

@[expose] noncomputable def twoPlaneRotation (K : Type) [Field K] [CharP K 2] :
    StatedSp 2 K := statedSpMap (ZMod.castHom (dvd_refl 2) K) 2 binaryRotation

theorem twoPlaneRotation_mem_commutator {K : Type} [Field K] [CharP K 2] :
    twoPlaneRotation K ∈ commutator (StatedSp 2 K) := by
  let f := statedSpMap (ZMod.castHom (dvd_refl 2) K) 2
  have h : twoPlaneRotation K ∈ (commutator (StatedSp 2 (ZMod 2))).map f :=
    Subgroup.mem_map.mpr ⟨binaryRotation, binaryRotation_mem_commutator, rfl⟩
  have hm : (commutator (StatedSp 2 (ZMod 2))).map f ≤ commutator (StatedSp 2 K) := by
    rw [commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hm h

theorem mat_twoPlaneRotation {K : Type} [Field K] [CharP K 2] :
    mat 2 K (twoPlaneRotation K) = fun i j =>
      (!![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) K) (finSumFinEquiv i) (finSumFinEquiv j) := by
  have hm : mat 2 K (twoPlaneRotation K) =
      (mat 2 (ZMod 2) binaryRotation).map (ZMod.castHom (dvd_refl 2) K) := rfl
  rw [hm, mat_binaryRotation]
  have htable :
      (!![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) K) =
      (!![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0] :
        Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  ext i j
  exact congrFun (congrFun htable (finSumFinEquiv i)) (finSumFinEquiv j)

theorem twoPlaneRotation_eq_weyl {K : Type} [Field K] [CharP K 2] :
    twoPlaneRotation K = longBlock K 2 1 WSL * permSp K (Equiv.swap (0 : Fin 2) 1) := by
  apply mat_injective
  rw [mat_twoPlaneRotation, map_mul, mat_longBlock, mat_permSp, coe_WSL]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Steinberg.Sp.blockMat, spIncl, inclMat, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, finSumFinEquiv]
  all_goals exact (CharTwo.neg_eq (1 : K)).symm

theorem twoPlaneRotation_pow_four {K : Type} [Field K] [CharP K 2] :
    twoPlaneRotation K ^ 4 = 1 := by
  rw [twoPlaneRotation, ← map_pow, binaryRotation_order.1, map_one]

theorem shortBlock_WSL_eq_permSp_swap {K : Type} [Field K] [CharP K 2]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    shortBlock K hij WSL = permSp K (Equiv.swap i j) := by
  have hW : (WSL : CFSG.LieType.Chevalley.SL2 K) * WSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_WSL]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  have hi : (WSL : CFSG.LieType.Chevalley.SL2 K)⁻¹ = WSL :=
    inv_eq_of_mul_eq_one_right hW
  apply mat_injective
  rw [mat_shortBlock, mat_permSp, hi, coe_WSL]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [CFSG.LieType.Steinberg.Sp.blockMat, spIncl, inclMat,
      Matrix.one_apply, Equiv.swap_apply_def, CharTwo.neg_eq]
  all_goals first | exact Ne.symm hbi | exact Ne.symm hbj | simp only [eq_comm]

theorem pairEmbed_twoPlaneRotation_eq_weyl {K : Type} [Field K] [CharP K 2]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    pairEmbed K hij (twoPlaneRotation K) = longBlock K n j WSL * permSp K (Equiv.swap i j) := by
  rw [twoPlaneRotation_eq_weyl,
    ← shortBlock_WSL_eq_permSp_swap (by decide : (0 : Fin 2) ≠ 1)]
  change spEmbed (pairMap i j) (pairMap_injective hij)
    (longBlock K 2 1 WSL * shortBlock K (by decide : (0 : Fin 2) ≠ 1) WSL) = _
  rw [map_mul, spEmbed_longBlock, pairMap_one]
  have hs : spEmbed (pairMap i j) (pairMap_injective hij)
      (shortBlock K (by decide : (0 : Fin 2) ≠ 1) WSL) = shortBlock K hij WSL := by
    have h := congrArg (fun f : CFSG.LieType.Chevalley.SL2 K →* StatedSp n K => f WSL)
      (spEmbed_comp_shortBlock hij)
    exact h
  rw [hs, shortBlock_WSL_eq_permSp_swap]

end CFSG.StandardType.QTwoSymplecticCav

end
