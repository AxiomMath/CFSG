module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireBase
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2Asm
public import CFSG.Quasithin.Vol2.Ch3E215MSplit
public import CFSG.Quasithin.Vol2.Ch3E215MP1
public import CFSG.Quasithin.Vol2.Ch3E215MP2
public import CFSG.Quasithin.Vol2.Ch3E215MP3
public import CFSG.Quasithin.Vol2.Ch3E215MP4
public import CFSG.Quasithin.Vol2.Ch3E215MP5
public import CFSG.Quasithin.Vol2.Ch3E215MP7
public import CFSG.Quasithin.Vol2.Ch3E215MP8
public import CFSG.Quasithin.Vol2.Ch3E215MSp4
public import CFSG.Quasithin.Vol2.Ch3E213MP6BK
public import CFSG.Quasithin.Vol2.Ch3E213MOLA10
public import CFSG.Quasithin.Vol2.Ch3E213MOLB10
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

theorem e215Member_holds
    : Ch3n.E215Member :=
  Ch3E215M.e215Member_of_packages e22StatementNoN_proved
      (Ch3E215M.pkgL2Paired215 C129Native.a38ForSQTKCat_proved)
      (Ch3E215M.pkgSzPaired215 C129Native.a38ForSQTKCat_proved)
      (Ch3E215M.pkgOddPaired215 C129Native.a38ForSQTKCat_proved) Ch3E215M.pkgBenderSingle215
      Ch3E215M.pkgL3215
      (pkgSp4215_of irrStatement_holds factSp4TransvW_holds Ch3E215M.Sp4.sp4MemberE215_holds
          (pkgSp4C2215 factSp4TransvW_holds factSp4CTwo_holds Ch3E215M.Sp4.sp4MemberE215_holds))
      Ch3E215M.pkgOddSingle215
      (Ch3E215M.pkgOddL3215_of OLA.kFactL3U3OuterInv_holds OLB.kFactL33NoQuadFour_holds)

end CFSG.Quasithin.Ch3E213M.Sp4C2
