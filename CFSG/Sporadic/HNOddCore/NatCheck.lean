module

public import CFSG.Sporadic.HNOddCore.InvData
public import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public import Certificates.Certificate2087

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

theorem nat_cert : natChecks = true :=
  Certificates.certificate2087.1

theorem natComm_cert : natCommChecks = true :=
  Certificates.certificate2087.2

end CFSG.Sporadic.HNOddCore.Native
