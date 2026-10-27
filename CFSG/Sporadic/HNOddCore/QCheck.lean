module

public import CFSG.Sporadic.HNOddCore.QData
public import CFSG.Sporadic.HNOddCore.InvArrays
public import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.Sporadic.HNOddCore.QData
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import Certificates.Certificate2089

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

theorem q_cert : qChecks = true :=
  Certificates.certificate2089

end CFSG.Sporadic.HNOddCore.Native
