module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireBase
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2Asm
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.Quasithin.Vol2.Ch3E213MOLB10
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WSplit
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WP1
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WP2
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WP3
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WP4
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WP5
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WSp4Mem
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WSp4C2

public section

namespace CFSG.Quasithin.Res2

theorem e215MemberW_of_sp4
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h22 : E2.E22StatementNoN) (hA : Ch3E213M.OL.KFactL3U3OuterInv)
    (hB : Ch3E213M.OL.KFactL33NoQuadFour) (h6 : PkgSp4215W) : E215MemberW :=
  e215MemberW_of_packages h22 (pkgL2Paired215W h38) (pkgSzPaired215W h38)
    (pkgOddPaired215W h38) pkgBenderSingle215W pkgL3215W h6 pkgOddSingle215W
    (pkgOddL3215W_of hA hB)

theorem e215MemberW_holds
    : E215MemberW :=
  e215MemberW_of_sp4 C129Native.a38ForSQTKCat_proved e22StatementNoN_proved
    Ch3E213M.OLA.kFactL3U3OuterInv_holds Ch3E213M.OLB.kFactL33NoQuadFour_holds
    (pkgSp4215W_of Ch3E213M.irrStatement_holds Ch3E213M.Sp4C2.factSp4TransvW_holds
      sp4MemberE215W_holds
      (pkgSp4C2215W Ch3E213M.Sp4C2.factSp4TransvW_holds Ch3E213M.Sp4C2.factSp4CTwo_holds
        sp4MemberE215W_holds))

end CFSG.Quasithin.Res2
