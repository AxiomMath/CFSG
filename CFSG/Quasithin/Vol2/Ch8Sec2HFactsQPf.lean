module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsQ9
public import CFSG.Quasithin.Background.HFCode22Q
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsQ

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H

theorem hQ82_holds :
    HQ82 := by
  intro V _ _ L X hLX hcase
  rcases hcase with ⟨n, hn, hL⟩ | h24 | h24c | ⟨h22, rfl⟩
  · exact two_lt_qOf_l3nine hLX hn hL
  · exact_mod_cast B45Mat.two_lt_qOf_code24 hLX h24
  · exact_mod_cast B45Mat.two_lt_qOf_cocode24 hLX h24c
  · exact_mod_cast B45Mat.two_lt_qOf_code22_self h22

end CFSG.Quasithin.H13
