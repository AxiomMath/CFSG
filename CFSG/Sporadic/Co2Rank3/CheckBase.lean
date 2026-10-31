
module

public import CFSG.Sporadic.Co2Cert.Check
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public import Certificates.Data.CFSGNative.Co2Rank3.Data
public import Mathlib.Data.Fintype.Basic
public import CFSG.Sporadic.Co2Rank3.CheckInputs
public import CFSG.Sporadic.Co2Rank3.CheckInputsT
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public meta import Certificates.Data.CFSGNative.Co2Rank3.Data
public meta import Mathlib.Data.Fintype.Basic

set_option compiler.extract_closed false

@[expose] public section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3.Native

def co2ColourT (s : ℕ) : Array ℕ :=
  CFSG.Sporadic.FischerOddCore.Native.colourT 2300 co2Nbr (idA 2300) (refineBase.take s) 3

end CFSG.Sporadic.Co2Rank3
