
module

public import CFSG.Sporadic.HNSchreier.FALocalCheckBase

public import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNSchreier.FAData
public import CFSG.Sporadic.HNSchreier.FALocalCheckInputs
public import Certificates.Certificate2097

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native

theorem fa_nat_cert : faNatChecks = true :=
  Certificates.certificate2097

end CFSG.Sporadic.HNSchreier.Native
