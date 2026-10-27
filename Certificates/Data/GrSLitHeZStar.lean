module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSCertInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentCheckInputs

public section

namespace Certificates.GrSLitHeZStar

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
  CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.GrSLit.HeldFix
  CFSG.ComponentClassification.GrSLit.HeGS

@[expose] def heZOuterTab : Tab := comp 8330 heCArrs[0]! heCArrs[0]!

@[expose] def heZD1Tab : Tab := comp 8330 (heDArr 0) (heDArr 0)

@[expose] def heZDYTab : Tab := comp 8330 (comp 8330 heZD1Tab (heDArr 2)) (heDArr 2)

@[expose] def heZD2Tab : Tab := comp 8330 heZDYTab (comp 8330 heZDYTab heZDYTab)

@[expose] def heZCommMod (t : Tab) (j : Nat) : Bool :=
  comp 32 t hfTTabs32[j]! == comp 32 hfTTabs32[j]! t ||
    comp 32 t hfTTabs32[j]! == comp 32 hfTTabs32[0]! (comp 32 hfTTabs32[j]! t)

@[expose] def heZSylowOK : Bool :=
  hfTEnum32.tabs.all fun t => !(allBelow 5 (heZCommMod t)) || comp 32 t t == idTab 32

@[expose] def heZWords : List (List Nat) :=
  [[], [2,2], [1,2,1], [0,0,2,1], [2,4,0,2], [0,4,2,1], [2], [4,3,1], [0,3,2,4], [0,4,2,3,4],
    [3,4,4,0,2], [0,3,1,4], [2,4,1], [0,1], [3,4,2,2], [2,0,3,2,4], [1,3,4], [0,1,3,4],
    [0,0,4,4,1], [3,3,4,2], [3,0,4,2], [3,4,4], [2,3,4], [2,3,4,0,2], [3,4,2], [1,3,0,4,2],
    [0,3,4,2,1], [3,1,2], [3,0,2], [2,4,4,1], [3,4], [3,0,4,4,1], [0,2], [4,2,3,4], [4,2,2],
    [3,1], [2,4,3,1,4], [3,2,2,4,1], [0,2,1], [4], [4,2,1], [0,2,2,4,1], [1], [1,2], [0,2,2],
    [3,1,4], [3,2,2], [4,1,2], [1,2,4,2,1], [4,1], [0,2,4], [4,4,3,4], [1,0,0,2], [2,4,2],
    [4,3,4], [4,0,2], [3,2,4,0,2], [4,2], [0,0,2,4,1], [2,2,4,1], [2,4,2,2], [4,4,1], [2,1],
    [0,0,2,4,2], [4,0,2,4], [4,3,3,1,2], [0,3,4,2], [3,0,2,1], [2,4,4], [0,2,4,1], [0,2,1,4],
    [2,4,1,2], [2,1,4], [0,0,2,4], [4,3,1,4], [3,2,4], [4,4], [0,4,2], [1,0,3,4,2], [3,3,2,4],
    [3,4,0,2], [4,3,4,2], [4,0,2,1], [2,2,4], [0,4,4,1], [0,2,4,2], [4,4,0,1], [0,0,2], [4,4,0,2],
    [3,4,4,2], [2,4,2,1], [3,3,1,2], [4,3,1,2], [4,1,4], [0,1,4], [4,4,3,1], [4,4,2], [2,4],
    [3,4,2,1], [4,0,2,4,1], [1,4], [4,0,1], [4,3,0,4,2], [3,2,2,4], [4,3,4,2,1]]

@[expose] def heZU (x : Nat) : Tab := wordTabS 105 heDGens (heZWords.getD x [])

@[expose] def heZTransOK : Bool := allBelow 105 fun x => (heZU x)[0]! == x

@[expose] def heZFixOK : Bool :=
  (heDGens[2]!)[79]! == 63 && (heDGens[2]!)[94]! == 86 && allBelow 105 fun x => x == 0 ||
    !((heDGens[2]!)[(heZU 79)[x]!]! == (heZU 63)[x]! &&
      (heDGens[2]!)[(heZU 94)[x]!]! == (heZU 86)[x]!)

@[expose] def heZUTab : Tab := heGSKTab (heGSComm2 heGSUComm)

@[expose] def heZT0UTab : Tab := comp 8330 (heGen 0) heZUTab

end Certificates.GrSLitHeZStar
