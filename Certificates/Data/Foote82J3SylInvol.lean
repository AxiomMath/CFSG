module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.CGT.Foote82.Proof511.J3Syl

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
  CFSG.ClassicalInvolution.J3Data

@[expose] def sqOneCount (_ : Unit := ()) : Nat :=
  countProducts 20520 (invoOK 20520) (chainTables 20520 sStrong sBase) (idT 20520)

end CFSG.CGT.Foote82.Proof511.J3Syl
