module

public import Certificates.Kernel.Census.Fi22PkT2A
public import Certificates.Kernel.Census.Fi22PkT2W
public import Certificates.Kernel.Census.Fi22PkT2K

public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open CFSG.KC.Census

@[expose] def fi22T2Root : RootConjP :=
  ⟨fi22T2X, fi22T2Xs, fi22T2Xi, fi22T2Rs, fi22T2Cjs, fi22T2Bs, fi22T2Im, fi22T2Wt,
    [fi22T2K0, fi22T2K1, fi22T2K2, fi22T2K3, fi22T2K4, fi22T2K5, fi22T2K6, fi22T2K7],
    fi22T2Kb, fi22T2Cs, fi22T2Gams, fi22T2Ga, fi22T2Gi, #[], fi22T2Cands⟩

end CFSG.ComponentClassification.RankTwoSporadic.Fi22
