module

public import CFSG.LocalAnalysis.StandardType.GGKG3Defs
public import CFSG.LocalAnalysis.StandardType.GGKG3ExData
public import CFSG.LocalAnalysis.StandardType.GGKG3K3dWeyl
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Sylow

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.StandardType.GGKG3.K3dCheck CFSG.StandardType.GGKG3.K3dWeyl

@[expose] noncomputable def k3Star (c : WeylGroup .E6) (y : Fin 6 → ZMod 7) : Fin 6 → ZMod 7 :=
  k3ActT (weylMat6 c⁻¹) y

theorem k3ActT_mul (A B : Matrix (Fin 6) (Fin 6) ℤ) (y : Fin 6 → ZMod 7) :
    k3ActT (A * B) y = k3ActT B (k3ActT A y) := by
  funext i
  simp only [k3ActT, Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem k3ActT_one (y : Fin 6 → ZMod 7) : k3ActT 1 y = y := by
  funext i
  simp [k3ActT, Matrix.one_apply, Finset.sum_ite_eq]

theorem k3Star_mul (c d : WeylGroup .E6) (y : Fin 6 → ZMod 7) :
    k3Star (c * d) y = k3Star c (k3Star d y) := by
  unfold k3Star
  rw [mul_inv_rev, weylMat6_mul, k3ActT_mul]

theorem k3Star_one (y : Fin 6 → ZMod 7) : k3Star 1 y = y := by
  unfold k3Star
  rw [inv_one, weylMat6_one, k3ActT_one]

theorem k3Star_smul (c : WeylGroup .E6) (a : ZMod 7) (y : Fin 6 → ZMod 7) :
    k3Star c (a • y) = a • k3Star c y :=
  k3ActT_smul _ _ _

theorem k3Star_inv_star (c : WeylGroup .E6) (y : Fin 6 → ZMod 7) :
    k3Star c⁻¹ (k3Star c y) = y := by
  rw [← k3Star_mul, inv_mul_cancel, k3Star_one]

theorem k3Star_apply (c : WeylGroup .E6) (y : Fin 6 → ZMod 7) (i : Fin 6) :
    k3Star c y i = k3Pair y (c⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
  unfold k3Star k3ActT k3Pair
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : (weylMat6 c⁻¹).mulVec (Pi.single i 1 : Fin 6 → ℤ) k = weylMat6 c⁻¹ k i := by
    rw [Matrix.mulVec_single_one]
    rfl
  have h3 := weylMat6_mulVec c⁻¹ (Pi.single i 1)
  have h : (weylMat6 c⁻¹ k i : ℤ) = (c⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) k := by
    rw [← congrFun h3 k]
    exact h2.symm
  rw [← h]

theorem weylMat6_w3 :
    weylMat6 w3 = Matrix.of kMw := by
  ext i j
  have h2 : weylMatrix w3 = CFSG.RankThree.Lattice.wordMat Tag.E6
      CFSG.LieType.SeitzGeneration.e6ThreeWord :=
    CFSG.HardMathSupport.Malle.E27Lie.ExcCross.weylMatrix_wordProd' Tag.E6
      CFSG.LieType.SeitzGeneration.e6ThreeWord
  rw [weylMat6_apply, h2, CFSG.LieType.SeitzGeneration.e6Three_wordMat]
  rfl

theorem kMw_cube :
    Matrix.of kMw * Matrix.of kMw * Matrix.of kMw = (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  decide +kernel

theorem k3Star_w3_inv
    {y : Fin 6 → ZMod 7} (hy : y ∈ k3Ex) : k3Star w3⁻¹ y = (2 : ZMod 7) • y := by
  unfold k3Star
  rw [inv_inv, weylMat6_w3]
  exact hy

theorem k3Star_w3
    {y : Fin 6 → ZMod 7} (hy : y ∈ k3Ex) : k3Star w3 y = (4 : ZMod 7) • y := by
  have hA : weylMat6 w3⁻¹ * weylMat6 w3 = 1 := by
    rw [← weylMat6_mul, inv_mul_cancel, weylMat6_one]
  rw [weylMat6_w3] at hA
  have hinv : weylMat6 w3⁻¹ = Matrix.of kMw * Matrix.of kMw := by
    calc weylMat6 w3⁻¹ = weylMat6 w3⁻¹ * (Matrix.of kMw * Matrix.of kMw * Matrix.of kMw) := by
          rw [kMw_cube, mul_one]
      _ = (weylMat6 w3⁻¹ * Matrix.of kMw) * Matrix.of kMw * Matrix.of kMw := by
          simp only [mul_assoc]
      _ = Matrix.of kMw * Matrix.of kMw := by rw [hA, one_mul]
  unfold k3Star
  rw [hinv, k3ActT_mul]
  have h2 : k3ActT (Matrix.of kMw) y = (2 : ZMod 7) • y := hy
  rw [h2, k3ActT_smul, h2, smul_smul]
  norm_num

end CFSG.StandardType.GGKG3
