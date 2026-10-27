
module

public import CFSG.YGroups.Model233FBase

public import CFSG.YGroups.Model233F.RawChain
public import CFSG.YGroups.CosetAction233
public import Certificates.Data.CFSGNative.YGroups.Model233FData
public import CFSG.YGroups.Model233FInputs
public import Certificates.Certificate10101
public meta import CFSG.YGroups.Defs
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.Model233FData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Certificate10095Base

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Certificates.CosetEnumeration (evalWord)

theorem ker_rho233F_le_ctil :
    rho233F.ker ≤ Ctil :=
  ker_rho233F_le_ctil_of_index index_ctil

end CFSG.YGroups
