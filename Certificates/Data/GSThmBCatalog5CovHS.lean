module

public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutNative
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.ComponentClassification.GSThmB.CovHS

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def t1Tab : Tab := natArr (hsCentTbl 5)

@[expose] def t2Tab : Tab := natArr (hsCentTbl 12)

@[expose] def yWord : List Nat := [3, 0, 0, 3, 2]

@[expose] def yTab : Tab := wordTabS 3850 hsC2Tabs yWord

@[expose] def kleinCheck : Bool :=
  permOK 3850 (hsCentTbl 5) && t1Tab.size == 3850 && permOK 3850 (hsCentTbl 12) &&
    t2Tab.size == 3850 && yWord.all (· < 4) &&
    J2Cover.fixedCount 3850 t1Tab == 170 && J2Cover.fixedCount 3850 t2Tab == 30 &&
    comp 3850 yTab yTab == idTab 3850 && !(yTab == idTab 3850) &&
    J2Cover.fixedCount 3850 yTab == 30 && J2Cover.fixedCount 3850 (comp 3850 t2Tab yTab) == 30

@[expose] def c4Tabs : Array Tab :=
  Array.ofFn (n := 4) fun k => natArr (hsCentTbl (k.val + 35))

@[expose] def c4Invs : Array Tab := c4Tabs.map (invTab 3850)

@[expose] def qWords : List (List Nat) :=
  [[0, 1, 0, 3, 0, 2, 1, 3], [0, 3, 0, 2, 1, 3, 0, 1], [1, 1, 0, 2, 3, 0, 1, 3],
    [0, 1, 3, 1, 1, 0, 2, 3]]

@[expose] def qGens : Array Tab :=
  Array.ofFn (n := 4) fun j => wordTabS 3850 c4Tabs (qWords.getD j.val [])

@[expose] def qEnum : Enum := enumBFS 3850 qGens 16

@[expose] def c4Enum : Enum := enumBFS 3850 c4Tabs 1920

@[expose] def outerCheck : Bool :=
  (allBelow 4 fun k =>
      permOK 3850 (hsCentTbl (k + 35)) && (natArr (hsCentTbl (k + 35))).size == 3850) &&
    qWords.all (fun w => w.all (· < 4)) &&
    enumOK 3850 qGens qEnum && qEnum.tabs.size == 16 &&
    normalOK 3850 qEnum.tabs c4Tabs c4Invs qGens &&
    enumOK 3850 c4Tabs c4Enum && c4Enum.tabs.size == 1920 &&
    (c4Enum.tabs.toList.filter (commAll 3850 qGens)).length == 16

end CFSG.ComponentClassification.GSThmB.CovHS
