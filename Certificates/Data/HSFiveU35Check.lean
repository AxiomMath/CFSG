module

public import Certificates.Data.HSFiveU35Data
public import Certificates.Data.MaxD2Heis

public section

namespace Certificates.HSU35

open CFSG.PSL3Four.Native Certificates.FusD2Perm Certificates.MaxD2Perm Certificates.MaxD2Heis
  Certificates.HSOver

@[expose] def uEnum : Enum := enumBFS 100 dataU.gT 126000

@[expose] def tabT : Tab := wT hsFiveDataP hsOverTW

@[expose] def checkUEnum (E : Enum) : Bool := enumOK 100 dataU.gT E && E.tabs.size == 126000

@[expose] def checkUCent (E : Enum) : Bool :=
  allBelow E.tabs.size fun k =>
    !(comp 100 E.tabs[k]! tabT == comp 100 tabT E.tabs[k]!) ||
      anyBelow 8 fun j => E.tabs[k]! == powT 100 tabT j

@[expose] def check19850 : Bool :=
  let E := uEnum
  checkUEnum E && checkUCent E

@[expose] def tabX : Tab := wT hsFiveDataP hsOverXW

@[expose] def tabY : Tab := wT hsFiveDataP hsOverYW

@[expose] def tabW : Tab := wT hsFiveDataP hsOverWW

@[expose] def tabC : Tab := wT hsFiveDataP hsOverCW

@[expose] def checkOrders : Bool :=
  powT 100 tabX 8 == idTab 100 && !(powT 100 tabX 4 == idTab 100) &&
    powT 100 tabY 3 == idTab 100 && !(tabY == idTab 100) &&
    powT 100 (comp 100 tabX tabY) 7 == idTab 100 && !(comp 100 tabX tabY == idTab 100) &&
    powT 100 tabT 8 == idTab 100 && !(powT 100 tabT 4 == idTab 100)

@[expose] def checkIdent : Bool :=
  wT dataU xyU0W == wT hsFiveDataP hsFiveUW && wT dataU xyV0W == wT hsFiveDataP hsFiveVW &&
    wT dataU xyTW == tabT && wT dataU xyWW == tabW && wT dataU xyCW == tabC &&
    wT dataU xyE1W == wT hsFiveDataP hsOverE1W && wT dataU xyE2W == wT hsFiveDataP hsOverE2W

@[expose] def checkTCent : Bool :=
  let rT := (hrEnum dataU).tabs
  allBelow rT.size fun k => !(comp 100 tabT rT[k]! == comp 100 rT[k]! tabT) || rT[k]! == idTab 100

@[expose] def checkW : Bool :=
  let wi := invTab 100 tabW
  let nT := (nEnum dataU).tabs
  let nIdx := indexOf nT
  wi.size == 100 && comp 100 wi tabW == idTab 100 && !found nIdx nT tabW &&
    anyBelow 8 fun j => comp 100 (comp 100 tabW tabT) wi == powT 100 tabT j

@[expose] def checkKernel : Bool :=
  let wi := invTab 100 tabW
  let ci := invTab 100 tabC
  let nT := (nEnum dataU).tabs
  let nIdx := indexOf nT
  wi.size == 100 && comp 100 wi tabW == idTab 100 && ci.size == 100 &&
    comp 100 ci tabC == idTab 100 &&
    allBelow nT.size fun k =>
      !(found nIdx nT (comp 100 (comp 100 wi nT[k]!) tabW) &&
          found nIdx nT (comp 100 (comp 100 ci nT[k]!) tabC)) || nT[k]! == idTab 100

@[expose] def e9Words : List (List Int) := [hsOverE1W, hsOverE2W]

@[expose] def e9Gens : Array Tab := (e9Words.map (wT hsFiveDataP)).toArray

@[expose] def e9Enum : Enum := enumBFS 100 e9Gens 9

@[expose] def checkE9 (E : Enum) : Bool :=
  enumOK 100 e9Gens E && E.tabs.size == 9 &&
    (allBelow E.tabs.size fun i => allBelow E.tabs.size fun j =>
      comp 100 E.tabs[i]! E.tabs[j]! == comp 100 E.tabs[j]! E.tabs[i]!) &&
    allBelow E.tabs.size fun i => powT 100 E.tabs[i]! 3 == idTab 100

@[expose] def uaWords : List (List Int) :=
  [hsFiveUW, hsFiveVW, hsFiveTW, hsFiveSW, hsOverGAW]

@[expose] def uaGens : Array Tab := (uaWords.map (wT hsFiveDataP)).toArray

@[expose] def checkUA : Bool :=
  invsOK 100 uaGens (uaGens.map (invTab 100)) &&
    wordT 100 uaGens (uaGens.map (invTab 100)) uaXW == tabX &&
    wordT 100 uaGens (uaGens.map (invTab 100)) uaYW == tabY

@[expose] def check19852 : Bool :=
  checkInv hsFiveDataP && checkOrders && checkIdent && checkTCent && checkW && checkKernel &&
    checkE9 e9Enum && checkUA

end Certificates.HSU35
