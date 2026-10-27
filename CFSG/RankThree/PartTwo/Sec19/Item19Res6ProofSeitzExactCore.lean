module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactMain
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactShift
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExactSmallKernel
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases

public section

open CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec19

theorem unitaryOuterHeisCoreExact_holds :
    UnitaryOuterHeisCoreExact := by
  intro ℓ f K _ h hq3 hq ω α hω hαN hnc
  by_cases h17 : 17 ≤ ℓ ^ f
  · exact exactClosure_eq_top_of_large h hq3 h17 hω hαN hnc
  have hf := h.one_le
  have hpow : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by omega : f ≠ 0) h.prime.one_lt
    omega
  have h14 := pow_ne_fourteen h.prime hf
  have hsmall : ℓ ^ f = 5 ∨ ℓ ^ f = 8 ∨ ℓ ^ f = 11 := by omega
  obtain ⟨s, hs, hsQ⟩ := shift_mem_exactClosure_small_kernel h hsmall hω hαN hnc
  have hle := fixU_le_exactClosure_of_shift h hq3 hω hαN hs hsQ
  have htop : outerHeisClosure ℓ f K ω α = ⊤ :=
    unitaryOuterHeisCore_of_finite_cases HeisSmall.outerB12AtCard_five
        HeisSmall.outerB12AtCard_eight HeisSmall.outerB12AtCard_eleven ℓ f K h hq3 hq ω α hω hαN hnc
  rw [htop] at hle
  exact top_le_iff.mp hle

theorem seitz199OuterUnitaryDiag_holds :
    Seitz199OuterUnitaryDiag :=
  seitz199OuterUnitaryDiag_of_exact unitaryOuterHeisCoreExact_holds

end CFSG.RankThree.PartTwo.Sec19
