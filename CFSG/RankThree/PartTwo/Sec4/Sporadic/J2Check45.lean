module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data45
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public import Certificates.Certificate8169
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

open CFSG.ComponentClassification.J2Cover CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Mathieu

theorem j2_check45_parts :
    chkElts45 = true ∧ chkEnum45 = true ∧
    chkLocal45 = true ∧ chkW = true ∧ chkS = true ∧ chkE0 = true ∧ chkVk = true :=
  Certificates.certificate8169.1

end CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
