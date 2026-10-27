
module

public import CFSG.Sporadic.Schreier.Co1RigidCheckBase

public import CFSG.Sporadic.Schreier.Co1SplitCheck
public import CFSG.Sporadic.Schreier.Co1LocalExtData
public import CFSG.Sporadic.Schreier.Co1RigidCert
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1LocalExtData
public meta import CFSG.Sporadic.Schreier.Co1RigidCert
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1RigidCheckInputs
public import Certificates.Certificate2145

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native

end Native

theorem rig_check : Native.rigCheck = true :=
  Certificates.certificate2145.1

theorem prop_check : Native.propCheck = true :=
  Certificates.certificate2145.2.1

theorem free_check : Native.freeCheck = true :=
  Certificates.certificate2145.2.2.1

theorem basis_check : Native.basisCheck = true :=
  Certificates.certificate2145.2.2.2.1

theorem cand_check : ∀ ε : Fin 8 → Bool, Native.candOK ε = true :=
  Certificates.certificate2145.2.2.2.2

end CFSG.Sporadic.Co1Schreier
