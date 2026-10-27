module

public import Certificates.Data.GH74.Ivk8Two
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import Certificates.Data.GH74.Ivk8Two
public meta import CFSG.Sporadic.Schreier.PairMcLCertInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative

public section

namespace Certificates.Ivk8Two.McL

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Th.Native

@[expose] def wordU1 : List ℤ :=
  [-2, -1, -2, -2, -1, -2, -2, -1, 2, 2, -1, -2, -2, -1, 2, 2, -1, -2, -2, -1, -2, -1, 2, -1, -2,
   -1, 2, 2, 1, -2, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
   1, 2, 2, 1, 2, -1, -2, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, 1, 2, 1, -2, -1, 2, -1, 2, 2,
   -1, -2, -2, -2, -1, -2, 1, 2, 1, 2, 1, -2, -2, 1, 2, 1, -2, -2, 1, 2, 2, 2, 1, 2, 2, 1, -2, 1,
   -2, -2]

@[expose] def wordU2 : List ℤ :=
  [2, 1, 2, 2, 1, -2, -2, 1, -2, -2, -1, 2, -1, 2, 2, -1, 2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 2, 1,
   -2, -2, 1, 2, 2, 1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, 2, -1, -2, -1, 2, 2, -1, 2,
   -1, -2, -1, -1, -2, -2, -1, 2, -1, 2, 2, -1, -2, -1, 2, 1, 2]

@[expose] def wordU3 : List ℤ :=
  [-2, -1, -2, -2, -1, -2, -2, -1, 2, 2, -1, -2, -2, -1, 2, 2, -1, -2, -2, -1, -2, -1, 2, -1, -2,
   -1, -2, -1, -2, -1, -2, -1, 2, 2, -1, -2, -2, -1, 2, -1, 2, 1, 2, 2, 2, 2, -1, -2, -2, -1, -2,
   -2, -1, 2, 2, -1, 2, 2, -1, 2, -1, -2, -1, -2, -1, 2, 2, -1, 2, -1, -2, -1, -2, -2, -2, -2,
   -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, 2]

@[expose] def wordX : List ℤ :=
  [2, 1, -2, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2,
   1, -2, 1, -2, -2, -1, -2, -1, 2, 2, -1, -2, -1, -2, -2, -1, 2, 2, -1, 2, -1, -2, -1, -2, -1,
   2, -1, 2, -1, 2, -1, -2, -2, -1, 2, -1, 2, 2, -1, -2, -2, -2, -1, -2, -1, -2]

@[expose] def wordY : List ℤ :=
  [-2, -2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, 1, 2,
   1, 2, 1, -2, 1, -2, -2, -1, 2, -1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2,
   1, 2, 2, 1, -2, 1, -2, -2, 1, 2, 2, 1, 2, 1, -2, -2, 1, -2, -1, 2, 2, -1, -2, -2, -1, -2, -1,
   -2]

@[expose] def gensT : List Table :=
  [arrTable 275 mclStrongArrs[0]!, arrTable 275 mclStrongArrs[1]!]

@[expose] def mclTwoOK : Bool := twoOKT 275 gensT [1] wordU1 wordU2 wordU3 wordX wordY

end Certificates.Ivk8Two.McL
