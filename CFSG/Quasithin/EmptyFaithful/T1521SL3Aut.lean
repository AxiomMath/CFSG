module

public import CFSG.Quasithin.EmptyFaithful.T1521SFam
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Syl
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Alt1
public import CFSG.Quasithin.EmptyFaithful.T1521SL3Alt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.L3Aut

theorem autFactL3_holds : AutFactL3 := by
  intro G _ _ L P hq hZ hty hP v hv _ hc l hl
  rcases hty with ⟨n, hn, hL⟩ | hL
  · exact centralizes_of_model_alt1 l3ModelAut_holds hn hL hP hv hc l hl
  · exact centralizes_of_model_alt2 l3ModelAut_holds hq hZ hL hP hv hc l hl

end CFSG.Quasithin
