
module

public import CFSG.Sporadic.Schreier.Co3SylowCheck
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs

@[expose] public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

def co3M1Levels : Array Level := rawLevels 276 co3M1Arrs co3M1BaseArr

end CFSG.Sporadic.Schreier.Co3
