
module

public import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public import CFSG.Sporadic.SuzOddCore.CertChainCheckBase
public meta import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public meta import CFSG.Sporadic.SuzOddCore.CertChainCheckBase

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def uRejectWord : List Int := [-6, -7, -9, -10, -3, -7, 5, 4, -7, -1, 2, 9, -7]

@[expose] def uStripWord (i : Nat) : List Int := (normalizingSiftWords.getD i []).flatten

end CFSG.Sporadic.SuzOddCore
