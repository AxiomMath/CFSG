module

public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.LieType.Multipliers.PresentedCover
public import CFSG.Sporadic.HN.F5Group
public import Certificates.Data.CFSGNative.HN.Data

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.Sporadic.F5 CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Bridge.TableSurj
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.LieType.Multipliers

abbrev HNJ : Type := J CFSG.Sporadic.HN.Native.hnData

end CFSG.Sporadic.Recognition.HNMultiplier
