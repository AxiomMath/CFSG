module

public import CFSG.Quasithin.Background.FFC1NonsplitOff
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B5FinS8

public section

namespace CFSG.Quasithin

namespace FFC

theorem b51IrrInputs_of_ffc
    (h42 : AsB42) (hI16 : AsI16Cover) (hSp : AsB51NonsplitOffSp4) :
    B5.B51IrrInputs :=
  ⟨h42, asB42Ident_of_b42 h42, asSp4S6, asS8D8, asOutAbelian, hI16, asB51NonsplitOff_of_sp4 hSp⟩

end FFC

end CFSG.Quasithin
