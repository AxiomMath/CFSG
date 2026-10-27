module

public import CFSG.Quasithin.Vol2.Ch3E213MSplit
public import CFSG.Quasithin.Vol2.Ch3E213MP1
public import CFSG.Quasithin.Vol2.Ch3E213MP2G
public import CFSG.Quasithin.Vol2.Ch3E213MP3E
public import CFSG.Quasithin.Vol2.Ch3E213MP4
public import CFSG.Quasithin.Vol2.Ch3E213MP4C7
public import CFSG.Quasithin.Vol2.Ch3E213MP5K
public import CFSG.Quasithin.Vol2.Ch3E213MP7
public import CFSG.Quasithin.Vol2.Ch3E213MP6AB
public import CFSG.Quasithin.Vol2.Ch3E213MP6D2
public import CFSG.Quasithin.Vol2.Ch3E213MP6EJ
public import CFSG.Quasithin.Vol2.Ch3E213MP8
public import CFSG.Quasithin.Vol2.Ch3E213MOLB10
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.Quasithin.Vol2.Ch3E213MP6BI
public import CFSG.Quasithin.Vol2.Ch3E213MG41F

public section

namespace CFSG.Quasithin.Ch3E213M

theorem e213Member_of
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h22 : E2.E22StatementNoN) (hW : FactSp4TransvW) (h4 : PkgSp4C2) : Ch3n.E213Member :=
  e213Member_of_packages h22 (pkgL2Paired h38) (pkgSzPaired h38) (pkgOddPaired h38)
      (pkgBenderSingle_of pkgBenderU3) pkgL3
      (pkgSp4_of pkgSp4Diag (pkgSp4Transv irrStatement_holds hW) h4 pkgSp4One) pkgOddSingle
      (pkgOddL3_of OLA.kFactL3U3OuterInv_holds OLB.kFactL33NoQuadFour_holds)

theorem e213Member_of_facts
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h22 : E2.E22StatementNoN) (hR : FactSp4TransvRefl) (hCTwo : FactSp4CTwo) :
    Ch3n.E213Member :=
  e213Member_of h38 h22 (G41.factSp4TransvW_of_refl hR)
    (pkgSp4C2W (G41.factSp4TransvW_of_refl hR) hCTwo)

end CFSG.Quasithin.Ch3E213M
