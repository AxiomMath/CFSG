module

public import Certificates.Kernel.Census.Fi22PkT0A
public import Certificates.Kernel.Census.Fi22PkT0W
public import Certificates.Kernel.Census.Fi22PkT0K

public section

set_option maxRecDepth 100000

set_option maxHeartbeats 0

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open CFSG.KC.Census

@[expose] def fi22T0Root : RootConjP :=
  ⟨fi22T0X, fi22T0Xs, fi22T0Xi, fi22T0Rs, fi22T0Cjs, fi22T0Bs, fi22T0Im, fi22T0Wt,
    [fi22T0K0, fi22T0K1, fi22T0K2, fi22T0K3, fi22T0K4, fi22T0K5, fi22T0K6, fi22T0K7, fi22T0K8],
    fi22T0Kb, fi22T0Cs, fi22T0Gams, fi22T0Ga, fi22T0Gi, #[], fi22T0Cands⟩

end CFSG.ComponentClassification.RankTwoSporadic.Fi22
