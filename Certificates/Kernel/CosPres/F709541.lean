module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import Certificates.Kernel.Bounds.Family
public import Mathlib

open CFSG.CosetTable CFSG.StandardType.ZS

public section

#kb_family "data/F709541.json.gz" 3887 7045483854960469900 (r0 := hsFiveRels)
  (r1 := restrictWords (subsetOf 5 [0, 1, 2, 3]) hsFiveRels) (r2 := hsSixRels)
  (r3 := restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) hsSixRels)
  (r4 := restrictWords (subsetOf 5 [0, 1, 2, 3])
    (restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) hsSixRels))

end
