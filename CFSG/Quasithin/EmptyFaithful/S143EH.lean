module

public import CFSG.Quasithin.EmptyFaithful.S143EG

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem lemma_14_3_18_a : S143.Lemma14318a := by
  intro G _ _ T M g c
  exact
    { v_eq := S143.v_eq_of c
      r_eq := S143.r_eq_of c.h1281 c.nonab c.goodElt (S143.E_eq_VZ c)
      i2_cent := S143.i2_cent_of c.h1281 c.nonab c.goodElt
      i2_sThree := S143.i2_sThree_of c.h1281 c.nonab c.goodElt
      r_fpf := S143.r_fpf_of c.h1281 c.nonab c.goodElt (S143.E_eq_VZ c)
      rq_index := S143.rq_index_of c
      rstar_card := S143.rstar_card_of c
      u_eq := S143.u_eq_of c }

end CFSG.Quasithin
