module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModV

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem lemma12_7_2_of
    (h1222 : Stmt12_2_2) (h128 : Stmt12_2_8) : Lemma12_7_2 := by
  intro G _ _ T L V _ h
  exact ⟨lemma12_7_2_zero h1222 h, lemma12_7_2_one h1222 h, lemma12_7_2_two h1222 h,
    lemma12_7_2_three h1222 h, lemma12_7_2_four h1222 h, lemma12_7_2_five h1222 h,
    lemma12_7_2_six h1222 h128 h⟩

end CFSG.Quasithin.H13.S127.Mod

end
