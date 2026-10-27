module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormOrthAbs
public import CFSG.Open.MatrixModelCore
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.HardMathSupport.Solomon.Coordinator

theorem s15k_norm_orth_matrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 2) (ι → ZMod 2)) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Fintype.card ι) (M : Matrix.GeneralLinearGroup ι (ZMod 2))
    (hM : ∀ g ∈ CFSG.MatrixModel.isometryCore (fun v => Q v),
      M * g * M⁻¹ ∈ CFSG.MatrixModel.isometryCore (fun v => Q v)) :
    M ∈ CFSG.MatrixModel.isometryCore (fun v => Q v) := by
  let b := Pi.basisFun (ZMod 2) ι
  have hmap : (i28_14_N_OG Q).map (mclt_glMatrixEquiv b).toMonoidHom =
      CFSG.MatrixModel.isometryCore (fun v => Q v) :=
    mclt_map_glMatrixEquiv_eq_closure b (fun v => by simp [b]) (fun g => i28_14_N_mem_OG)
  have key : ∀ N : Matrix.GeneralLinearGroup ι (ZMod 2),
      N ∈ CFSG.MatrixModel.isometryCore (fun v => Q v) ↔
        (mclt_glMatrixEquiv b).symm N ∈ i28_14_N_OG Q := by
    intro N
    rw [← hmap, Subgroup.mem_map_equiv]
  rw [key]
  have hg : ∀ x ∈ i28_14_N_OG Q, (mclt_glMatrixEquiv b).symm M * x *
      ((mclt_glMatrixEquiv b).symm M)⁻¹ ∈ i28_14_N_OG Q := by
    intro x hx
    have hx' : mclt_glMatrixEquiv b x ∈ CFSG.MatrixModel.isometryCore (fun v => Q v) := by
      rw [key, MulEquiv.symm_apply_apply]
      exact hx
    have := hM _ hx'
    rw [key] at this
    simpa using this
  have hd : 3 ≤ Module.finrank (ZMod 2) (ι → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact h3
  exact s15k_norm_orth_abs Q hQ hd hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
