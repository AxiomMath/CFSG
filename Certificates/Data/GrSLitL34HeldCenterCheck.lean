module

public import CFSG.RankThree.PartOne.KS.HeFiveCheckInputs
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Mathlib

public section

namespace CFSG.ComponentClassification.GrSLit.L34HeldCenter

open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.Sporadic.HeldB

@[expose] def heFiveNoFourOK : Bool :=
  allLt heFiveC0Cert.pts.size fun i =>
    !(eqA 8330 (compA 8330 (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!)
        (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!)) (idA 8330)) ||
      eqA 8330 (compA 8330 heFiveC0Cert.pts[i]! heFiveC0Cert.pts[i]!) (idA 8330) ||
      !(siftA 8330 heLevels heBase.toArray 0 heFiveC0Cert.pts[i]!)

end CFSG.ComponentClassification.GrSLit.L34HeldCenter
