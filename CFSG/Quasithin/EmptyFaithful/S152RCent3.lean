module

public import CFSG.Quasithin.EmptyFaithful.S152QF
public import CFSG.Quasithin.EmptyFaithful.S152RU33
public import CFSG.Quasithin.EmptyFaithful.S152RLn2
public import CFSG.Quasithin.EmptyFaithful.S152RTits
public import CFSG.Quasithin.EmptyFaithful.S152RD4

public section

namespace CFSG.Quasithin

theorem cent3RankF2_holds :
    Cent3RankF2 := by
  intro X _ _ hX l hl2 hl1 P hP hP9 hP3
  rcases hX with h | h | h | h | h
  · exact noE9CentralizedByInvolution_of_isPSU_three_three h l hl2 hl1 P hP hP9 hP3
  · exact noE9CentralizedByInvolution_of_psl_four_two h l hl2 hl1 P hP hP9 hP3
  · exact noE9CentralizedByInvolution_of_psl_five_two h l hl2 hl1 P hP hP9 hP3
  · exact noE9CentralizedByInvolution_of_reeTitsModel_tits h l hl2 hl1 P hP hP9 hP3
  · exact noE9CentralizedByInvolution_of_trialityD4_two h l hl2 hl1 P hP hP9 hP3

end CFSG.Quasithin
