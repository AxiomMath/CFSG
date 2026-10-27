module

public import CFSG.Sporadic.Schreier.ONOuterData
public import CFSG.Sporadic.Schreier.ONGlue
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import CFSG.Sporadic.Schreier.ONGlue
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.PSL3Four.Native

@[expose] def t32Enum : Enum := enumBFS 32 Data.T32Chain.generators 600

@[expose] def m120Enum : Enum := enumBFS 120 Data.M120Chain.generators 50000

end CFSG.ONSchreier
