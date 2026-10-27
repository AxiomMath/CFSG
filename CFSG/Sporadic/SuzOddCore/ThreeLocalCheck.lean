module

public import CFSG.Sporadic.SuzOddCore.GammaCheck
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.GammaCheck
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.SuzOddCore.ThreeLocalCheckInputs
public import Certificates.Certificate2308

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

theorem threeLocal_check :
    threeChecks fullExtArrs (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) = true :=
  Certificates.certificate2308

end CFSG.Sporadic.SuzOddCore
