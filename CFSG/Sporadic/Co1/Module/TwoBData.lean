
module

public import CFSG.Sporadic.Co1.Module.TwoBDataBase

public import CFSG.Sporadic.Co1.Module.InvData
public import CFSG.Sporadic.Co1.Module.OddCentCard
public import CFSG.Sporadic.Co1.Module.TwoBTree
public import CFSG.Sporadic.Co1.Module.TwoBDataInputs
public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
public import Certificates.Certificate10077
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import Certificates.Data.CFSGNative.Co1.OddCent
public meta import Certificates.Data.CFSGNative.Co1.TwoB

public section

namespace CFSG.Sporadic.Co1.Module.TwoB

theorem twoB_ok : ∃ W : TwoBW, TwoBOK W :=
  Certificates.certificate10077.1

theorem centB_ok : centB = true :=
  Certificates.certificate10077.2

end CFSG.Sporadic.Co1.Module.TwoB
