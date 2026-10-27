module

public import CFSG.Sporadic.SmallOddCore.HeLocalCheck2Inputs

public section

namespace CFSG.Quasithin.E6.HeInvPerfect

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

@[expose] def heX1CommGens : Array Tab :=
  #[commTab 42 heXTabs[2]! heXTabs[8]! heXInvs[2]! heXInvs[8]!,
    commTab 42 heXTabs[3]! heXTabs[8]! heXInvs[3]! heXInvs[8]!]

@[expose] def heX1CommEnum : Enum := enumBFS 42 heX1CommGens 10752

end CFSG.Quasithin.E6.HeInvPerfect
