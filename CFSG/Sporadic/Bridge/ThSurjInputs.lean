
module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.Sporadic.ThSchreier.Enc8
public import Certificates.Data.CFSGNative.Th.Core
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Thompson

public section

namespace CFSG.Sporadic.Bridge.Th

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native TauCeti

abbrev pres : GroupPresentation := TauCeti.Sporadic.Thompson.presentation

end CFSG.Sporadic.Bridge.Th
