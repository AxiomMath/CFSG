
module

public import CFSG.Sporadic.Co2Rank3.CheckBase

public import CFSG.Sporadic.Co2Cert.Check
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public import Certificates.Data.CFSGNative.Co2Rank3.Data
public import Mathlib.Data.Fintype.Basic
public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import CFSG.Sporadic.Co2Rank3.CheckInputsT
public import Certificates.Certificate10079
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public meta import Certificates.Data.CFSGNative.Co2Rank3.Data
public meta import Mathlib.Data.Fintype.Basic

set_option compiler.extract_closed false

public section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3.Native

theorem co2Rank3_check : co2Rank3TOK = true :=
  Certificates.certificate10079

end CFSG.Sporadic.Co2Rank3
