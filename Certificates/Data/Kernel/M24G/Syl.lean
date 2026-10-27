module

public import Certificates.Data.CFSGNative.AS91.M24Syl
public import Certificates.Data.Kernel.M24G.Duad
public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Data.Kernel.M24G.Todd

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def sylS0BT : List (Nat × Nat × Nat) := Native.s0Tabs.map fun a => imgTab a.toList

@[expose] def sylS0FixOn (gs : List (Array Nat)) : Bool :=
  gs.all fun g => imgF (imgTab g.toList) 255 == 255 &&
    imgTrioF g.toList Native.baseTrio == Native.baseTrio &&
    imgSextF g.toList Native.baseSext == Native.baseSext &&
    imgSextF g.toList Native.pairPart == Native.pairPart

@[expose] def sylTripleF (t : List Nat) (x : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (t.getD x.1 0, t.getD x.2.1 0, t.getD x.2.2 0)

@[expose] def sylTripleSteps : List (Nat × Nat × Nat → Nat × Nat × Nat) :=
  Native.s0Tabs.map fun g => sylTripleF g.toList

@[expose] def sylOSPF (t : List Nat) (x : Native.OSP) : Native.OSP :=
  (imgF (imgTab t) x.1, imgSextF t x.2.1, imgSextF t x.2.2)

@[expose] def sylOSPSteps : List (Native.OSP → Native.OSP) :=
  Native.lTabs.map fun g => sylOSPF g.toList

@[expose] def sylSpF (t : List Nat) (L : List Nat) : List Nat :=
  sortN (L.map (toddActF (imgTab t)))

@[expose] def sylSpSteps : List (List Nat → List Nat) :=
  Native.genTabs.map fun g => sylSpF g.toList

@[expose] def sylFixedOn (bts : List (Nat × Nat × Nat)) : Bool :=
  Native.allLt 2048 (fun m => !(bts.all fun bt => toddActF bt m == m) || m == 0 || m == 31) &&
    bts.all fun bt => toddActF bt 31 == 31

@[expose] def sylSeen : List Nat → Nat → Bool
  | [], _ => true
  | c :: cs, M => !M.testBit c && sylSeen cs (M ||| (1 <<< c))

@[expose] def sylClsF (SL : List (List Nat)) : Bool :=
  SL.length == 1771 && sylSeen (SL.map Native.clsOf) 0 && Native.clsOf Native.baseSext == 31

@[expose] def sylTrioDetF (TS : List (List Nat)) : Bool :=
  allIdx (fun p r => p == 0 || !((TS.headD []).all fun q => r.contains q)) TS 0

@[expose] def sylV0F (SL TS : List (List Nat)) : Bool :=
  sortN (0 :: (TS.headD []).map fun q => Native.clsOf (SL.getD q [])) == Native.v0List &&
    Native.closedXor Native.v0List && Native.closedXor Native.vpList

@[expose] def sylClsMask (SL : List (List Nat)) : Nat := orMask (SL.map Native.clsOf)

@[expose] def sylCand (K v w : Nat) : Bool :=
  K.testBit v && K.testBit (31 ^^^ v) && v != 0 && v != 31 && w != 0 && w != 31 && w != v &&
    w != (31 ^^^ v) && K.testBit w && K.testBit (31 ^^^ w) && K.testBit (v ^^^ w) &&
    K.testBit (31 ^^^ v ^^^ w)

@[expose] def sylInv (v w : Nat) : Bool :=
  sylS0BT.all fun bt =>
    (Native.sp8 v w).contains (toddActF bt v) && (Native.sp8 v w).contains (toddActF bt w)

@[expose] def sylRow (K v w : Nat) : Bool :=
  !(sylCand K v w) || !(sylInv v w) || sortN (Native.sp8 v w) == Native.v0List ||
    sortN (Native.sp8 v w) == Native.vpList

@[expose] def sylMove (v : Nat) : Option Nat :=
  (sylS0BT.map fun bt => toddActF bt v).find? fun u =>
    !(u == 0 || u == 31 || u == v || u == (31 ^^^ v))

@[expose] def sylSpanV (K v : Nat) : Bool :=
  !(K.testBit v && K.testBit (31 ^^^ v) && v != 0 && v != 31) ||
    match sylMove v with
    | some u => [u, u ^^^ 31, u ^^^ v, u ^^^ 31 ^^^ v].all (sylRow K v)
    | none => Native.allLt 2048 (sylRow K v)

@[expose] def sylSpanOn (K : Nat) : Bool := Native.allLt 2048 (sylSpanV K)

end CFSG.KC.M24G
