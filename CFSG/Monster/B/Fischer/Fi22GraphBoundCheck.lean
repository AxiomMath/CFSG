
module

public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckBase

public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.Data.Fintype.Basic
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Basic
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckInputs
public import Certificates.Certificate3153
public import Certificates.Certificate3153Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.FischerOddCore.Native

theorem fi22GraphBound_check :
    adjOK 3510 fi22OrigArrs fi22Nbr fi22N0List = true ∧
    boundsOK 3510 fi22Nbr (idA 3510) fi22GraphBase fi22GraphOrbitBounds 4 = true :=
  Certificates.certificate3153

end CFSG.Monster.B.Fischer
