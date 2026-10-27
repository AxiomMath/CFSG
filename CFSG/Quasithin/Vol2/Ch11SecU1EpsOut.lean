module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IC
public import CFSG.Quasithin.Vol2.Ch11SecU1L33I
public import CFSG.Quasithin.Vol2.Ch11SecU1U3O
public import CFSG.Quasithin.Vol2.Ch11SecU1U3R
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin Vol2.Ch11.SecU1

theorem e114ResRestL3EpsOut_holds : E114ResRestL3EpsOut := by
  intro G _ _ T _ hFs hT hFT ⟨s, p, hp, hp2, h4, h4', hP, hTL⟩
  have : Fact p.Prime := ⟨hp⟩
  cases s with
  | true =>
    have h43 : p % 4 = 3 := h4 rfl
    by_cases hp3 : p = 3
    · subst hp3
      exact L33.nParam_le_one_of_psl3_three A38c15.sl3OddIrr hFs hP hT.1 hFT (hTL rfl)
    · have hp7 : 7 ≤ p := by
        have := hp.two_le
        omega
      exact L3I.nParam_le_one_of_psl3_outer A38c15.sl3OddIrr hp hp7 h43 hFs hP hT.1 hFT
        (hTL rfl)
  | false =>
    have h41 : p % 4 = 1 := h4' rfl
    by_cases hp5 : p = 5
    · subst hp5
      exact U3.nParam_le_one_of_psu3_five hP hFs hT hFT
    · exact U3.nParam_le_one_of_psu3_of_ne_five hp5 h41 hP hFs hT hFT

theorem e114OneResRest_holds : E114OneResRest :=
  e114OneResRest_of_L3EpsOut e114ResRestL3EpsOut_holds

end CFSG.Quasithin.E2.E22N
