module

public import CFSG.Quasithin.Vol2.Ch11SecOE9Q
public import CFSG.Quasithin.Vol2.Ch11SecOE8W

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin


theorem e114TwistedUpperSp4_holds : E114TwistedUpperSp4 :=
  fun _ _ _ _ _ hs hT hFT _ _ hS htw => nParam_le_of_isPSp4_of_twisted hS hs hT hFT htw

theorem e114LieCited_holds : SecE3.E114LieCited :=
  e114LieCited_of_twistedUpperSp4 e114TwistedUpperSp4_holds

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
