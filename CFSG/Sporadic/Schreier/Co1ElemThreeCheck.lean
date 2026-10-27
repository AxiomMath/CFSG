module

public import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public import Certificates.Certificate2133

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

end Native

theorem elem_check : Native.elemCheck = true :=
  Certificates.certificate2133.1

theorem e_check : Native.eCheck = true :=
  Certificates.certificate2133.2.1

theorem eigen_check : Native.eigenCheck = true :=
  Certificates.certificate2133.2.2

end CFSG.Sporadic.Co1Schreier
