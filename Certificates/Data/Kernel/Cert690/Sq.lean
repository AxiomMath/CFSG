module

public import Certificates.Data.Kernel.Cert690.Base
public import CFSG.GF2Type.Smith1979W3.Cert690.Check
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

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690

@[expose] def innW (t : Array ℕ) : ℕ :=
  2 * (t[2]! % 2) + t[4]! % 2 + 8 * (t[8]! % 2) + 4 * (t[16]! % 2) + 32 * (t[32]! % 2) +
    16 * (t[64]! % 2)

@[expose] def innGuess (t : Array ℕ) : Option ℕ :=
  if innTab (2 * innW t) == t then some (2 * innW t) else none

end CFSG.KC.C690

end
