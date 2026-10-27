module

public import CFSG.Sporadic.HNOddCore.InvArrays
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.OrbitCert
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import CFSG.Sporadic.HNOddCore.ChainUtil
public meta import CFSG.Sporadic.HNOddCore.OrbitCert
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import Certificates.Certificate2091

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

theorem natChain_cert : natChainChecks = true :=
  Certificates.certificate2091.1

theorem orbits_cert : orbitChecks = true :=
  Certificates.certificate2091.2

end CFSG.Sporadic.HNOddCore.Native
