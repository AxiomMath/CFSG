module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs

public section

namespace Certificates.Seitz77Sec27

open CFSG.ComponentClassification.HarrisLit.EndB CFSG.ComponentClassification.J2Cover
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def j2U0 : Table := wordTbl 315 c2BGens [2, 2, 2]

@[expose] def j2U0Check : Bool :=
  c2BGens.all (fun g => permOK 315 g) && permOK 315 j2U0 && involOK 315 j2U0 &&
    c2BGens.all (fun g => commTT 315 j2U0 g) &&
    !tblEq 315 j2U0 (arrTable 315 autStrong[0]!)

end Certificates.Seitz77Sec27
