module

public import Certificates.Data.Kernel.Cert690.CensusS
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Defs
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils

public section

namespace CFSG.KC.C690S

open CFSG.GF2Type.Smith1979W3.Cert690

@[expose] def bindS (minus : Bool) (B : SBase) : Bool :=
  B.og == oGensC minus && B.omg == omegaGensC minus && B.kpg == kPGLGens &&
    B.pglOK == !minus && B.nS * B.sing.length == (if minus then 51840 else 40320)

end CFSG.KC.C690S

end
