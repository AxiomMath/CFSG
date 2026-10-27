module

public import CFSG.Sporadic.Schreier.Co1RigidCheck
public import Std.Data.HashSet
public meta import CFSG.Sporadic.Schreier.Co1RigidCheck
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1LocalExtData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1GenCheckInputs
public import Certificates.Certificate2136

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

end Native

theorem gen_check : Native.genCheck = true :=
  Certificates.certificate2136

end CFSG.Sporadic.Co1Schreier
