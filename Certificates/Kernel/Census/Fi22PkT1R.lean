module

public import Certificates.Kernel.Census.Fi22PkT1A
public import Certificates.Kernel.Census.Fi22PkT1W
public import Certificates.Kernel.Census.Fi22PkT1K

public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open CFSG.KC.Census

@[expose] def fi22T1Root : RootConjP :=
  ⟨fi22T1X, fi22T1Xs, fi22T1Xi, fi22T1Rs, fi22T1Cjs, fi22T1Bs, fi22T1Im, fi22T1Wt,
    [fi22T1K0, fi22T1K1, fi22T1K2, fi22T1K3, fi22T1K4, fi22T1K5, fi22T1K6, fi22T1K7, fi22T1K8, fi22T1K9, fi22T1K10, fi22T1K11],
    fi22T1Kb, fi22T1Cs, fi22T1Gams, fi22T1Ga, fi22T1Gi, #[], fi22T1Cands⟩

end CFSG.ComponentClassification.RankTwoSporadic.Fi22
