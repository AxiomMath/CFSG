
module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Schreier.Enum3
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Enum3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu

def sqA (t : Array ℕ) : Array ℕ := compA 315 t t

def sqIterA : ℕ → Array ℕ → Array ℕ
  | 0, t => t
  | n + 1, t => sqIterA n (sqA t)

def isTwoA (t : Array ℕ) : Bool := eqA 315 (sqIterA 7 t) (idA 315)

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
