module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireBase
public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2Asm
public import CFSG.Quasithin.Vol2.Ch3E213MWireAll
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

theorem e213Member_holds
    : Ch3n.E213Member :=
  e213Member_of_facts C129Native.a38ForSQTKCat_proved e22StatementNoN_proved
    factSp4TransvRefl_holds factSp4CTwo_holds

end CFSG.Quasithin.Ch3E213M.Sp4C2
