module

public import Certificates.Kernel.Census.Fi22PkT2R
public import Certificates.Kernel.Census.Fi22PkT1R
public import Certificates.Kernel.Census.Fi22PkT0R

public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open CFSG.KC.Census

@[expose] def fi22RootsC : List RootConjP := [fi22T2Root, fi22T1Root, fi22T0Root]

@[expose] def fi22Ks : List Nat := [10, 16, 13]

end CFSG.ComponentClassification.RankTwoSporadic.Fi22
