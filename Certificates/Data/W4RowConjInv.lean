module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2.Native

@[expose] def conjInvCheck (n : ℕ) (t h x : PArr) : Bool :=
  eqA n (compA n (compA n t.1 (compA n (compA n h.1 x.1) h.2)) t.2)
    (compA n (compA n h.1 x.2) h.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
