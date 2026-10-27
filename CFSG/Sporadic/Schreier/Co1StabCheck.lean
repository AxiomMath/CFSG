
module

public import CFSG.Sporadic.Schreier.Co1StabCheckBase

public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public import CFSG.Sporadic.Schreier.Co1StabData
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public import Certificates.Certificate2148

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

end Native

theorem stab_orb_check : Native.stabOrbCheck = true :=
  Certificates.certificate2148.1

theorem stab_x_check : Native.stabXCheck = true :=
  Certificates.certificate2148.2.1

theorem wit_check : Native.witCheck = true :=
  Certificates.certificate2148.2.2.1

theorem fix_check : Native.fixCheck = true :=
  Certificates.certificate2148.2.2.2.1

theorem mem_check : Native.memCheck = true :=
  Certificates.certificate2148.2.2.2.2

end CFSG.Sporadic.Co1Schreier
