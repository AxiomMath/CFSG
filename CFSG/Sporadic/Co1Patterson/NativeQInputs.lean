module

public import Certificates.Data.CFSGNative.Co1Schreier.Base

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native

@[noinline, expose] def qExtraOK (Ra : Rows) (Qg : List Rows) : Bool :=
  Qg.all (fun q => mul q q == one || mul q q == Ra) &&
    Qg.all (fun p => Qg.all (fun q => mul p q == mul q p || mul p q == mul Ra (mul q p)))

end CFSG.Sporadic.Co1Patterson.Native
