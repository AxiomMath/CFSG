module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.Quasithin.Background.HZCoc24C
public import CFSG.Quasithin.Background.HZCode22B
public import CFSG.Quasithin.Background.HZL34B

public section

namespace CFSG.Quasithin.H13

theorem hZ82_holds :
    HZ82 := by
  intro V _ _ H e z h hz1 hS
  obtain ⟨S, hSH, hS, hzS⟩ := hS
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact CFSG.Quasithin.H.L34Z.hzConcl_of_binaryNine h hz1 hSH hS hzS
  · exact CFSG.Quasithin.H.Code22.hzConcl_of_code22 h hz1 hSH hS hzS
  · exact CFSG.Quasithin.H.Coc24.hzConcl_of_cocode24 h hz1 hSH hS hzS

end CFSG.Quasithin.H13
