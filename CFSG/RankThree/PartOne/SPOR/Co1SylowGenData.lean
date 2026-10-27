module

public import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
public import Certificates.Data.CFSGNative.Co1.TwoB

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative

@[noinline, expose] def co1SylowGenOK (derivs : List (List Int)) (i₁ i₂ : Nat) : Bool :=
  let D := dag co1PlaneBase derivs
  pow (D.1.getD (i₁ - 1) one) 5 == one && pow (D.1.getD (i₂ - 1) one) 5 == one

end CFSG.RankThree.PartOne.SPOR
