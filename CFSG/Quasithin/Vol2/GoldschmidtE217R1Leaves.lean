module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R1
public import CFSG.Quasithin.Background.C129NativeLight
public import CFSG.Quasithin.Vol2.Ch3E213MP6BB
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.Quasithin.Vol2.Ch3E213MOLB10
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Ch3E213M

namespace E217R1

theorem r1Leaves_of
    (hT : FactSp4TransvW) (hC : FactSp4CTwo) : R1Leaves where
  a38 := C129Native.a38ForSQTKCat_proved
  irr := Ch3E213M.irrStatement_holds
  g41 := hT
  cTwo := hC
  ivk12 := CFSG.GH74.GLS.IVK.ivk_1_2_general
  ivk13a := CFSG.GH74.GLS.IVK.ivk_1_3a
  ivk13b := CFSG.GH74.GLS.IVK.ivk_1_3b
  coat := fun _ _ _ hF hq _ _ _ e _ hu =>
    CFSG.GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hF hq e hu
  outerInv := Ch3E213M.OLA.kFactL3U3OuterInv_holds
  noQuad := Ch3E213M.OLB.kFactL33NoQuadFour_holds

end E217R1

end CFSG.Quasithin
