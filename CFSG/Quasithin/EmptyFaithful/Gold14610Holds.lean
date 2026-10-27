module

public import CFSG.Quasithin.EmptyFaithful.Gold14610Assemble
public import CFSG.Quasithin.EmptyFaithful.Gold14610Blocks
public import CFSG.Quasithin.EmptyFaithful.Gold14610CmpMain
public import CFSG.Quasithin.EmptyFaithful.Gold14610NoCase12
public import CFSG.Quasithin.EmptyFaithful.Gold14610Lift
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618Struct

public section


namespace CFSG.Quasithin

theorem input14610ListW_holds
    : Gold14610.Input14610ListW :=
  Gold14610.input14610ListW_of_pieces Gold14610.gold14610NoCase12_proved
      (Gold14610.gold14610LiftOfStruct Gold14610.Struct.gold14610F618Struct_proved)
      gold14610Compare_holds gold14610BlockOrders_holds

end CFSG.Quasithin
