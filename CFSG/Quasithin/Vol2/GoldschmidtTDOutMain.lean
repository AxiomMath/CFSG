module

public import CFSG.Quasithin.Vol2.GoldschmidtTDOutLin
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutSp
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAlt
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutSpor
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutExc

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin.H13.OutTwoNilp

theorem outTwoNilpotentFact_holds
    : OutTwoNilpotentFact := by
  intro S _ _ hsimple hnab hlist
  have := hsimple
  refine outTwoNilpotent_of_twoNilpotent_outer ?_
  rcases hlist with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, -, -, hmodel⟩ | ⟨⟨f, hf⟩ | hTits⟩ | ⟨n, -, hm⟩ |
      ⟨s, hs, ⟨e⟩⟩
  · exact twoNilpotent_outer_of_alt hn5 hn8 e
  · rcases hmodel with ⟨f, -, hm⟩ | hm | hm
    · exact twoNilpotent_outer_of_psl_two hnab hm
    · exact twoNilpotent_outer_of_three hnab (Or.inl ⟨rfl, rfl⟩) hm
    · exact twoNilpotent_outer_of_three hnab (Or.inr ⟨rfl, rfl⟩) hm
  · rcases hf with ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf1, hm⟩ | ⟨-, -, hm⟩ |
      ⟨-, -, hm⟩
    · exact twoNilpotent_outer_of_psl_two hnab hm
    · exact twoNilpotent_outer_of_three hnab (Or.inl ⟨rfl, rfl⟩) hm
    · exact twoNilpotent_outer_of_three hnab (Or.inr ⟨rfl, rfl⟩) hm
    · exact twoNilpotent_outer_of_psp_two hf2 hm
    · exact twoNilpotent_outer_of_G2 hf2 hm
    · exact twoNilpotent_outer_of_trialityD4 hf1 hm
    · exact twoNilpotent_outer_of_twistedF4 hm
    · exact twoNilpotent_outer_of_suzuki hm
  · exact twoNilpotent_outer_of_tits hTits
  · exact twoNilpotent_outer_of_psl_two_one hnab hm
  · by_cases hJ4 : s = .J4
    · subst hJ4
      exact twoNilpotent_outer_of_J4 e
    · refine twoNilpotent_outer_of_sporadic_ne_J4 ?_ hJ4 e
      simp only [CFSG.SectionRank.sqtkSporadicNames, Finset.mem_insert, Finset.mem_singleton]
      tauto

end CFSG.Quasithin.H13
