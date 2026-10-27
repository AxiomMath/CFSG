module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Defs
public import CFSG.Quasithin.EmptyFaithful.S1421QShape1
public import CFSG.Quasithin.EmptyFaithful.S1421QShape2bMain

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem e22InputBig (h38 : Vol2Native.A38ForSQTKCat) : E22InputBig := by
  intro G _ _ T M H K hStar hmin hsq hK hHK hcases
  unfold E22CasesBig at hcases
  dsimp only at hcases
  rcases hcases with ⟨hker, ⟨t, ht, hne, hM⟩, m, hm, hty, hB⟩ |
      ⟨hTK, hker, ⟨m, hBen, hB⟩ | ⟨m, hm, hty, hdiag, hB⟩⟩
  · exact case1_shape h38 hStar hmin hsq hK hHK hker ht hne hM hm hty hB
  · exact case2a_shape hStar hmin hK hHK hTK hker hBen hB
  · exact Case2b.case2b_shape hmin hK hHK hTK hker hm hty hdiag hB

end CFSG.Quasithin.F146Field
