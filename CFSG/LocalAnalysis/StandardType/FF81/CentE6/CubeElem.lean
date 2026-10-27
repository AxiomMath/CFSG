module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Std
public import CFSG.RankThree.GF2n.Smith81.S81A5Fixed
import CFSG.RankThree.GF2n.Smith81.S81NBasis
import CFSG.RankThree.GF2n.Smith81.S81NTk

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

theorem cubeAct_elem_cubeBasis {i j : Fin 6} (hij : i ≠ j) (I : Set.powersetCard (Fin 6) 3) :
    cubeAct (elem i j) (A5Cube.cubeBasis (ZMod 2) I) =
      if h : j ∈ I.val ∧ i ∉ I.val then
        A5Cube.cubeBasis (ZMod 2) I + A5Cube.cubeBasis (ZMod 2) (A5Cube.replSet I i j h.1 h.2)
      else A5Cube.cubeBasis (ZMod 2) I := by
  have hmat : ((elem i j : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      Matrix.transvection i j 1 := by
    unfold elem
    rw [dif_neg hij]
    exact Matrix.SpecialLinearGroup.transvection_coe hij 1
  have helem : Matrix.SpecialLinearGroup.toGL (elem i j) =
      A5Cube.transvGL (ZMod 2) i j hij 1 := by
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, A5Cube.transvGL_val, hmat]
  have hcube : cubeAct (elem i j) =
      A5Cube.rho (ZMod 2) (A5Cube.transvGL (ZMod 2) i j hij 1) := by
    unfold cubeAct
    rw [helem]
  rw [hcube, A5Cube.rho_transvGL_cubeBasis_gen (K := ZMod 2) i j hij 1 I]
  by_cases h : j ∈ I.val ∧ i ∉ I.val
  · simp only [dif_pos h, one_smul]
  · simp only [dif_neg h]

end CFSG.StandardType.FF81.CentE6
