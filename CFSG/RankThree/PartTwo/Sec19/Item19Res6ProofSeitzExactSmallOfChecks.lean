module

public import CFSG.LieType.SeitzGeneration.ShiftSmallSound
public import CFSG.LieType.SeitzGeneration.ShiftSmallData
public import CFSG.LieType.SeitzGeneration.HeisSmallCases
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExact
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem shift_mem_exactClosure_of_checks (h5 : shiftCheck 5 QExt.omega shiftTable5 = true)
    (h8 : shiftCheck 8 QExt.omega shiftTable8 = true)
    (h11 : shiftCheck 11 QExt.omega shiftTable11 = true) {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 5 ∨ ℓ ^ f = 8 ∨ ℓ ^ f = 11) {ω α : K}
    (hω : IsPrimitiveRoot ω 3) (hα : α ^ (ℓ ^ f + 1) = 1) (hαc : ¬ ∃ μ : K, μ ^ 3 = α) :
    ∃ s : unitarySU ℓ f K 3, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS ∧
      s ∈ Subgroup.closure (outerHeisExactFix ℓ f K ω α) := by
  have hq3 : 3 ∣ ℓ ^ f + 1 := by
    rcases hq with hq | hq | hq <;> rw [hq] <;> norm_num
  rcases hq with hq | hq | hq
  · obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q5) h hq3 (by rw [card_q5, hq])
      isPrimitiveRoot_omega hω
    exact shift_mem_exact_of_check h ι hι hιω hq hα hαc h5
  · obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q8) h hq3 (by rw [card_q8, hq])
      isPrimitiveRoot_omega hω
    exact shift_mem_exact_of_check h ι hι hιω hq hα hαc h8
  · obtain ⟨ι, hι, hιω⟩ := exists_ringHom_omega (L := Q11) h hq3 (by rw [card_q11, hq])
      isPrimitiveRoot_omega hω
    exact shift_mem_exact_of_check h ι hι hιω hq hα hαc h11

end CFSG.RankThree.PartTwo.Sec19
