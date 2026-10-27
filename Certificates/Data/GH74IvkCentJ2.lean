module

public import Certificates.Data.GH74EvSporCheck
public meta import Certificates.Data.GH74EvSporCheck

public section

namespace Certificates.IvkCent

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.J2Cover
  CFSG.GH74.Generic.S45.EvSpor

@[expose] def j2ChainTbls : List (List Table) :=
  chainTables 315 CFSG.Sporadic.Schreier.PairNative.j2StrongArrs CFSG.Sporadic.Schreier.PairJ2.baseArr

@[expose] def centKbPred (g : Table) : Bool := commTT 315 g j2KbA && commTT 315 g j2KbB

@[expose] def centKbOuterPred (g : Table) : Bool := centKbPred (compT 315 g j2OuterTbl)

@[expose] def j2CentInnerCount : Nat := countProducts 315 centKbPred j2ChainTbls (idT 315)

@[expose] def j2CentOuterCount : Nat := countProducts 315 centKbOuterPred j2ChainTbls (idT 315)

end Certificates.IvkCent
