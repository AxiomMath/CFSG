module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.Quasithin.Background.HZCoc24C

public section

namespace CFSG.Quasithin.H13

theorem hFus82_holds :
    HFus82 := by
  intro V _ _ H z h hz1 hS
  obtain ⟨S, hSH, hS, hzS⟩ := hS
  exact CFSG.Quasithin.H.Coc24.exists_fus_of_cocode24 h hz1 hSH hS hzS

end CFSG.Quasithin.H13
