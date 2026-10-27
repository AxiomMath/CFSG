module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactSmallOfChecks
import all CFSG.LieType.SeitzGeneration.HeisSmallCheck
import all CFSG.LieType.SeitzGeneration.HeisSmallModel

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem shiftCheck_five : shiftCheck 5 QExt.omega shiftTable5 = true := by decide +kernel

theorem shiftCheck_eight : shiftCheck 8 QExt.omega shiftTable8 = true := by decide +kernel

theorem shiftCheck_eleven : shiftCheck 11 QExt.omega shiftTable11 = true := by decide +kernel

theorem shift_mem_exactClosure_small_kernel {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 5 ∨ ℓ ^ f = 8 ∨ ℓ ^ f = 11) {ω α : K}
    (hω : IsPrimitiveRoot ω 3) (hα : α ^ (ℓ ^ f + 1) = 1) (hαc : ¬ ∃ μ : K, μ ^ 3 = α) :
    ∃ s : unitarySU ℓ f K 3, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS ∧
      s ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) :=
  shift_mem_exactClosure_of_checks shiftCheck_five shiftCheck_eight shiftCheck_eleven h hq hω hα
    hαc

end CFSG.RankThree.PartTwo.Sec19
