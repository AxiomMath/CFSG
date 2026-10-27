module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Cases
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618

public section

namespace CFSG.Quasithin.F6

open InspRest

theorem inspF618Rest_holds :
    InspF618Rest := by
  intro D _ _ H₁ H₂
  have s3 := fun h : IsF618CaseThree H₁ H₂ => spec_caseThree h
  have s4 := fun h : IsF618CaseFour H₁ H₂ =>
    spec_of_sqWitness typeL2One_of_mulEquiv (sqWitness_caseFour h)
  have s5 := fun h : IsF618CaseFive H₁ H₂ =>
    spec_of_sqWitness typeL2One_of_mulEquiv (sqWitness_caseFive h)
  have s6 := fun h : IsF618CaseSix H₁ H₂ =>
    spec_of_sqWitness typeSix_of_mulEquiv (sqWitness_caseSix h)
  have s7 := fun h : IsF618CaseSeven H₁ H₂ =>
    spec_of_sqWitness typeSeven_of_mulEquiv (sqWitness_caseSeven h)
  have s8 := fun h : IsF618CaseEightCat H₁ H₂ =>
    spec_of_sqWitness typeEight_of_mulEquiv (sqWitness_caseEight h)
  have s9 := fun h : IsF618CaseNineCat H₁ H₂ =>
    spec_of_sqWitness typeNine_of_mulEquiv (sqWitness_caseNine h)
  have s10 := fun h : IsF618CaseTen H₁ H₂ =>
    spec_of_sqWitness typeTen_of_mulEquiv (sqWitness_caseTen h)
  have s11 := fun h : IsF618CaseEleven H₁ H₂ =>
    spec_of_sqWitness typeTen_of_mulEquiv (sqWitness_caseEleven h)
  have s12 := fun h : IsF618CaseTwelve H₁ H₂ =>
    spec_of_sqWitness isM12_of_mulEquiv (sqWitness_caseTwelve h)
  have s13 := fun h : IsF618CaseThirteen H₁ H₂ =>
    spec_of_sqWitness isM12_of_mulEquiv (sqWitness_caseThirteen h)
  refine ⟨fun h => ?_, fun h => ?_, fun h => (s6 h).2, fun h => (s7 h).2, fun h => (s8 h).2,
    fun h => (s9 h).2, fun h => ?_, fun h => ?_⟩
  · rcases h with h | h | h | h | h | h | h | h | h | h | h
    · exact (s3 h).1
    · exact (s4 h).1
    · exact (s5 h).1
    · exact (s6 h).1
    · exact (s7 h).1
    · exact (s8 h).1
    · exact (s9 h).1
    · exact (s10 h).1
    · exact (s11 h).1
    · exact (s12 h).1
    · exact (s13 h).1
  · rcases h with h | h | h
    · exact (s3 h).2
    · exact (s4 h).2
    · exact (s5 h).2
  · rcases h with h | h
    · exact (s10 h).2
    · exact (s11 h).2
  · rcases h with h | h
    · exact (s12 h).2
    · exact (s13 h).2

end CFSG.Quasithin.F6
