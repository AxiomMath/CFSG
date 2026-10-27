module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireBase
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2Asm
public import CFSG.Quasithin.Vol2.GoldschmidtE217B1Final
public import CFSG.Quasithin.Vol2.GoldschmidtE217R1Leaves
public import CFSG.Quasithin.Vol2.GoldschmidtE217NCMain
public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

theorem e217NonsolvableNarrow_holds
    : E2.E217NonsolvableNarrow :=
  E217R4.e217NonsolvableNarrow_of_leaf (E217R1.r1Leaves_of factSp4TransvW_holds factSp4CTwo_holds)
      e22StatementNoN_proved E217R3.kFactL3U3NotOddCube_holds E217L27.r3Pkg2c7_holds

end CFSG.Quasithin.Ch3E213M.Sp4C2
