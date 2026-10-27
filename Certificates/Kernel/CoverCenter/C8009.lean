module

public import Certificates.Data.CoverCenterThreeMcL
public import Certificates.Kernel.Bounds.Family

open CFSG.SectionRank.Native CFSG.CosetTable

public section

namespace CFSG.SectionRank.Native

abbrev mclGammaRestr := restrictWords (subsetOf 7 [0, 6]) mclGammaWords

end CFSG.SectionRank.Native

#kb_family "data/C8009.json" 2383 1578238740703190395 (r0 := mclGammaWords)
  (r1 := mclGammaRestr)

end
