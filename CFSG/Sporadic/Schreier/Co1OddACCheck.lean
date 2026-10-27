module

public import CFSG.Sporadic.Schreier.Co1OddData
public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Co1.Module.InvData
public import Certificates.Data.CFSGNative.Co1.Odd
public meta import CFSG.Sporadic.Schreier.Co1OddData
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.Sporadic.Schreier.Co1OddACCheckInputs
public import Certificates.Certificate2142

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

end Native

theorem odd_ac_check : Native.oddACCheckOf Native.oddACRegs = true :=
  Certificates.certificate2142.1

theorem odd_ac_counts : Native.oddACCountsOf Native.oddACRegs = true :=
  Certificates.certificate2142.2.1

theorem odd_ac_x : Native.oddACXOf (Native.fullOrb 2) Native.oddACRegs = true :=
  Certificates.certificate2142.2.2

end CFSG.Sporadic.Co1Schreier
