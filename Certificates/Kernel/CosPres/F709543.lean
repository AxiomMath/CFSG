module

public import CFSG.Certificates.CosetTablePresented
public import CFSG.LocalAnalysis.StandardType.GGZSNFourInputs
public import Certificates.Kernel.Bounds.Family
public import Mathlib

open CFSG.CosetTable CFSG.StandardType.ZS

public section

#kb_family "data/F709543.json.gz" 3826 5791707981882290773 (r0 := n4Rels)
  (r1 := restrictWords (subsetOf 4 [0, 1, 2]) n4Rels) (r2 := en4Rels)
  (r3 := restrictWords (subsetOf 5 [0, 1, 2, 3]) en4Rels)
  (r4 := restrictWords (subsetOf 4 [0, 1, 2])
    (restrictWords (subsetOf 5 [0, 1, 2, 3]) en4Rels))

end
