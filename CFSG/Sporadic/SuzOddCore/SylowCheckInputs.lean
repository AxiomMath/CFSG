module

public import CFSG.Sporadic.SuzOddCore.InvTCheck
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native

@[expose] def sylowInvs : Array Tab := invSylowArrs.map (invTab 1782)

@[expose] def sylowEnum : Enum := enumBFS 1782 invSylowArrs 16384

@[expose] def fusionEnum (r : Nat) : Enum :=
  orbitBFS 1782 invSylowArrs sylowInvs (invFusionRepArr r) 1000

@[expose] def fusionEnums : Array Enum := Array.ofFn (n := 21) fun r => fusionEnum r.val

@[expose] def isInvTab (t : Tab) : Bool := comp 1782 t t == idTab 1782 && !(t == idTab 1782)

@[expose] def fusionCase (r : Nat) : Nat := invFusionCases.getD r 0

@[expose] def caseTabs (F : Array Enum) (i : Nat) : List Tab :=
  ((List.range 21).filter fun r => fusionCase r == i).flatMap fun r => F[r]!.tabs.toList

@[expose] def caseCounts : List Nat := [528, 95, 192, 96]

@[expose] def inT (g : Array Nat) : Bool := inM g || inM (compA 1782 vArr g)

@[expose] def fusionRecOK (r : Nat) (F E : Enum) (idx : Std.HashMap Tab Nat) : Bool :=
  let c := invFusionConjArr r
  orbitOK 1782 invSylowArrs sylowInvs (invFusionRepArr r) F &&
    F.tabs.size == invFusionSizes.getD r 0 &&
    permOK 1782 (invFusionRepArr r) && isInvTab (invFusionRepArr r) &&
    found idx E.tabs (invFusionRepArr r) &&
    permOK 1782 c && (invCand 1782 c).size == 1782 && inT c &&
    decide (fusionCase r < 4) && (tArr (fusionCase r)).size == 1782 &&
    conjTab 1782 c (invCand 1782 c) (tArr (fusionCase r)) == invFusionRepArr r

@[expose] def sylowChecks (E : Enum) (F : Array Enum) : Bool :=
  let idx := indexOf E.tabs
  (allBelow 11 fun k => permOK 1782 invSylowArrs[k]! && inT invSylowArrs[k]!) &&
    enumOK 1782 invSylowArrs E && E.tabs.size == 16384 &&
    (E.tabs.toList.filter isInvTab).length == 911 &&
    F.size == 21 &&
    (allBelow 21 fun r => fusionRecOK r F[r]! E idx) &&
    (allBelow 21 fun r => allBelow 21 fun r' =>
      r == r' || notInOK F[r]!.tabs (invFusionRepArr r')) &&
    coverOK 1782 E.tabs (F.map Enum.tabs) &&
    allBelow 4 fun i => decide (caseTabs F i).Nodup && (caseTabs F i).length == caseCounts.getD i 0

end CFSG.Sporadic.SuzOddCore
