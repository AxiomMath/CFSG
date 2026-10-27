module

public import Certificates.Data.Kernel.M24G.Img
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Data.Kernel.O8.NodeM
public import Certificates.Data.CFSGNative.AS91.M24Todd

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G CFSG.KC.O8

@[expose] def packBits : List Bool → Nat
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * packBits l

@[expose] def colsOf : Nat → List Nat → List Nat
  | 0, _ => []
  | n + 1, V => packBits (V.map fun v => v.testBit 0) :: colsOf n (V.map (· / 2))

@[expose] def toddActF (bt : Nat × Nat × Nat) (m : Nat) : Nat :=
  Native.actM Native.ccEColsN (imgF bt (Native.actM Native.liftEColsN m))

@[expose] def toddVals : List (List Nat) :=
  List.range 2048 :: Native.lTabs.map fun a => (List.range 2048).map (toddActF (imgTab a.toList))

@[expose] def nzMask (CS : List (List Nat)) (u : Nat) : Nat :=
  CS.foldr (fun cs acc => Native.actM cs u ||| acc) 0

@[expose] def full2048 : Nat := 2 ^ 2048 - 1

@[expose] def kerMask (CS : List (List Nat)) (u : Nat) : Nat := full2048 ^^^ nzMask CS u

@[expose] def badMask (br : List Nat) : Nat :=
  packBits ((List.range 2048).map fun w => !Native.toddOctsKer br w)

@[expose] noncomputable def uniqRowF (CS : List (List Nat)) (bad u : Nat) : Bool :=
  decide (popcM swarK (kerMask CS u) < 512) || kerMask CS u &&& bad == 0

@[expose] noncomputable def uniqLoopF (CS : List (List Nat)) (bad : Nat) : Bool :=
  (List.range 2048).all fun u => u == 0 || uniqRowF CS bad u

@[expose] noncomputable def toddUniqF : Bool :=
  uniqLoopF (toddVals.map (colsOf 11)) (badMask (Native.octsT Native.baseTrio))

@[expose] def toddIntCk (T : Array (Nat × Nat × Nat)) (S : Array (List Nat)) : Bool :=
  let K0 := (List.range 2048).filter (Native.toddOctsKer (Native.octsT Native.baseTrio))
  K0.length == 512 && Native.toddIntReps T S K0

@[expose] def toddSextCk (SL : List (List Nat)) : Bool :=
  let K0 := (List.range 2048).filter (Native.toddOctsKer (Native.octsS SL.toArray[0]!))
  K0.length == 128 && SL.length == Native.nSext &&
    allIdx (fun q s => q == 0 || K0.any fun w => !(Native.toddOctsKer (Native.octsS s) w)) SL 0

end CFSG.KC.M24G
