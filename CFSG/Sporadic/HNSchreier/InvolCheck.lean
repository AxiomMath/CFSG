
module

public import CFSG.Sporadic.HNSchreier.InvolCheckBase

public import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public import Certificates.Certificate2099

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native

theorem invol_cert : involChecks rowsA rowsB (rowsOf 5 133 LocalData.normalizerPayload)
    (rowsOf 5 133 LocalData.involutionPayload) tauIdx labMasks = true :=
  Certificates.certificate2099

end CFSG.Sporadic.HNSchreier.Native
