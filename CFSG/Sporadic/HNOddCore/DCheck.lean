
module

public import CFSG.Sporadic.HNOddCore.DCheckBase

public import CFSG.Sporadic.HNOddCore.InvArrays
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import Certificates.Certificate2084
public import Certificates.Certificate2084Base

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native InvData

theorem data_cert : dataChecks = true :=
  Certificates.certificate2084

end CFSG.Sporadic.HNOddCore.Native
