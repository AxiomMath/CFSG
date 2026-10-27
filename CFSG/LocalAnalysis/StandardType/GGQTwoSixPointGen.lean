module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointSu
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGenAux
import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGenAux2

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan
open CFSG.GH74.Uniqueness.SU.SU5 (F4c)

section Gen

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem nativeSu_closure_top (hK : Nat.card K = 4) :
    Subgroup.closure (Set.range (nativeSu hK)) = ⊤ := by
  refine eq_top_of_fourBlock_of_swaps hK (N := 6) (by norm_num)
    (Subgroup.closure (Set.range (nativeSu hK))) ?_ ?_
  · have h := qTwoSixGen_block0123_le hK
    simpa [qTwoSixGen_J0123] using h
  · intro i j hij g hg
    have hi5 : i.val < 5 := by omega
    let i5 : Fin 5 := ⟨i.val, hi5⟩
    have hgi : g = nativeSu hK (qTwoSixGen_swapIdx i5) := by
      apply Subtype.ext
      apply Units.ext
      ext a b
      rw [hg, qTwoSixGen_nativeSu_swap_matrix hK i5]
      have hii : i = i5.castSucc := Fin.ext rfl
      have hjj : j = i5.succ := Fin.ext hij.symm
      rw [hii, hjj]
    rw [hgi]
    exact Subgroup.subset_closure ⟨_, rfl⟩

theorem card_closure_chart5 (hK : Nat.card K = 4) :
    13685760 ≤ Nat.card (Subgroup.closure (nativeSu hK '' {i | i ∈ subsetOf 18 chart5})) :=
  qTwoSixGen_chart5_lower hK

end Gen

end CFSG.StandardType.QTwo.SixPoint

end
