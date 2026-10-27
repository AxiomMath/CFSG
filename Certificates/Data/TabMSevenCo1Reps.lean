module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Sporadic.Co1Schreier.Native Timmesfeld.Co1Seven

@[expose] def repSevenA : Rows :=
  #[
    14627922, 14228896, 15776775, 4500447, 1151164, 5532769,
    11746319, 16087689, 12950052, 14969194, 2302544, 6855821,
    7281635, 7455901, 1289946, 10707542, 13483804, 13914326,
    12184100, 9242168, 1282411, 12667060, 7330836, 15005803]

@[expose] def repSevenB : Rows :=
  #[
    7647789, 7365394, 12683041, 6347120, 8357349, 9390163,
    3133208, 4304025, 10595912, 1701823, 3510748, 2918636,
    14826886, 13619866, 10078951, 1883794, 5434314, 12274235,
    4396728, 5413413, 5515565, 2318525, 10110741, 7102525]

@[expose] def sevenRepsOK (aR bR : Rows) : Bool :=
  let rs := (gDag aR bR).1
  rowAt rs iS == repSevenA && rowAt rs iT == repSevenB

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
