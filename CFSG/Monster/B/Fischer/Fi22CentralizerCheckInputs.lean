
module

public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def fi22FixOrbit0 : Array (List ℕ) × Array ℕ × Array ℕ :=
  translateSearch fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 6)[0]!) 3511

@[expose] def fi22FixOrbit1 : Array (List ℕ) × Array ℕ × Array ℕ :=
  translateSearch fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 6)[1]!) 3511

@[expose] def fi22FixOrbitZ : Array (List ℕ) × Array ℕ × Array ℕ :=
  translateSearch fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 1)[0]!) 3510

end CFSG.Monster.B.Fischer
