module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.Quasithin.Background.HCocL34
public import CFSG.Quasithin.Background.HCocCode22
public import CFSG.Quasithin.Background.HCocCoc24

public section

namespace CFSG.Quasithin.H13

theorem hCoc82_holds :
    HCoc82 := by
  intro V _ _ H e z h hz1 hS δ hδ hR
  obtain ⟨S, hSH, hS, hzS⟩ := hS
  rcases h with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · exact CFSG.Quasithin.H.L34Z.coc_of_binaryNine h hz1 hSH hS hzS hδ hR
  · exact CFSG.Quasithin.H.Code22.coc_of_code22 h hz1 hSH hS hzS hδ hR
  · exact CFSG.Quasithin.H.Coc24.coc_of_cocode24 h hz1 hSH hS hzS hδ hR

end CFSG.Quasithin.H13
