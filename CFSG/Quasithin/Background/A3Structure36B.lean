
module


public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.A3Structure36BCases

public section

namespace CFSG.Quasithin

theorem a36_caseB (hF : A36CaseBFacts) : A36CaseBStatement := by
  intro X _ h
  obtain ⟨K, hK⟩ := A36B.exists_kernelSetup hF h
  refine ⟨?_, ?_, A36B.a36_extra hF h⟩
  · by_cases h5 : IsSL2 5 (X ⧸ CFSG.fittingSubgroup X)
    · exact Or.inr (A36B.case4 hF h hK h5)
    · exact Or.inl (A36B.case3 hF h hK h5)
  · refine ⟨A36B.fitting_eq_oddCore h hK, A36B.quotient_fitting_isQuasisimple h hK,
      Or.inl ⟨A36B.generalizedFitting_eq_fitting h, A36B.relIndex_fitting_radical h hK⟩,
      ?_, ?_⟩
    · rw [A36B.commutator_radical_eq_fitting hF h hK,
        A36B.commutator_fitting_top_eq hF.l2mult h hK]
    · have e : X ⧸ ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ ≃*
          X ⧸ CFSG.fittingSubgroup X :=
        QuotientGroup.quotientMulEquivOfEq (A36B.commutator_radical_eq_fitting hF h hK)
      exact A36B.isQuasisimple_of_mulEquiv e.symm (A36B.quotient_fitting_isQuasisimple h hK)

end CFSG.Quasithin
