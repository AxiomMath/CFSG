module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoLin
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoRest
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoExc
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryU4
public import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Kinds


theorem k419UnitaryChevTwo_of
    (hD4 : Sec21.TrialityD4EvenThreeRankTwo)
    (hF4 : Sec21.TwistedF4EvenThreeRankTwo) : K419UnitaryChevTwo := by
  intro G _ _ L hL h46 a haN ha3 haC K hKle hKc hU
  obtain ⟨m, hm, ⟨e⟩⟩ := hU
  obtain ⟨hm3, ⟨c⟩⟩ := HeringUnitary.UCfg.exists_of_component hL haN ha3 haC hKle hKc hm e
  have ha3' : a ^ 3 = 1 := by
    rw [← ha3]
    exact pow_orderOf_eq_one a
  rcases h46 with (⟨n, hn, hφ | hφ | hφ | hφ | hφ⟩ |
      ⟨f, hG2 | hD4' | hSz | hF4' | hTits⟩) | ⟨n, hn, hSL⟩
  · obtain ⟨φ⟩ := hφ
    exact HeringUnitary.chevTwo_projSL_two ha3' c hn φ
  · obtain ⟨φ⟩ := hφ
    exact HeringUnitary.chevTwo_projSL_three ha3' c hn φ
  · obtain ⟨φ⟩ := hφ
    exact HeringUnitary.chevTwo_projSU_three ha3' c hn φ
  · obtain ⟨φ⟩ := hφ
    exact HeringUnitary.chevTwo_projSp_two ha3' c hn φ
  · obtain ⟨φ⟩ := hφ
    exact (HeringUnitary.false_of_projSU_four c hn φ).elim
  · exact HeringUnitary.chevTwo_G2 ha3' c hG2
  · exact HeringUnitary.chevTwo_trialityD4 hD4 ha3' c hD4'
  · exact HeringUnitary.chevTwo_suzuki c hSz
  · exact HeringUnitary.chevTwo_twistedF4 hF4 ha3' c hF4'
  · exact HeringUnitary.chevTwo_tits c hTits
  · obtain ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := hSL
    · exact HeringUnitary.chevTwo_statedSL_three ha3' c hK φ
    · exact HeringUnitary.chevTwo_statedSU_three ha3' c hn hK φ

theorem k419UnitaryChevTwo_holds :
    K419UnitaryChevTwo :=
  k419UnitaryChevTwo_of Sec21.trialityD4EvenThreeRankTwo_holds
    Sec21.ReeF4ThreeLocalProof.twistedF4EvenThreeRankTwo_holds

end Kinds

end CFSG.RankThree.PartTwo.Sec4
