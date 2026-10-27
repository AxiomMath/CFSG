module

public import CFSG.Sporadic.Schreier.Co1OddACCheck
public import CFSG.Sporadic.Co1.Module.TwoBData
public meta import CFSG.Sporadic.Schreier.Co1OddData
public meta import CFSG.Sporadic.Schreier.Co1OddACCheck
public meta import CFSG.Sporadic.Co1.Module.TwoBData
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co1Schreier

namespace Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

@[expose] def oddBRegs : Array (Array Nat) :=
  runRows CFSG.Sporadic.Co1.Module.TwoB.initRowsB Data.oddBProg

@[expose] def oddProdRows (G : Array (Array Nat)) (ws : List (List (Nat × Nat))) : Array Nat :=
  ws.foldl (fun acc w => mulRows 24 acc (lineRows G w)) (idRows 24)

@[expose] def oddPerfOK (G : Array (Array Nat)) (ws : List (List (Nat × Nat))) (t : Array Nat) :
    Bool :=
  ws.length == 8 && oddProdRows G ws == t &&
    [(0, 2), (1, 3), (4, 6), (5, 7)].all fun p =>
      mulRows 24 (lineRows G ws[p.1]!) (lineRows G ws[p.2]!) == idRows 24

@[expose] def oddBCheckOf (R : Array (Array Nat)) (s : Array Nat) : Bool :=
  validRows s && [9, 14, 19, 24].all (fun i => validRows (oddReg R i) &&
      mulRows 24 (oddReg R i) s == mulRows 24 s (oddReg R i) &&
      isFixedN (transposeRows 24 (oddReg R i)) CFSG.Sporadic.Co1.Module.code4) &&
    powRows 24 (oddReg R 9) 3 == idRows 24 && powRows 24 (oddReg R 19) 3 == idRows 24 &&
    powRows 24 (oddReg R 14) 5 == idRows 24 && powRows 24 (oddReg R 24) 5 == idRows 24 &&
    powRows 24 (mulRows 24 (oddReg R 9) (oddReg R 19)) 15 != idRows 24 &&
    powRows 24 (mulRows 24 (oddReg R 14) (oddReg R 24)) 15 != idRows 24 &&
    oddPerfOK #[oddReg R 9, oddReg R 14] Data.oddPerfX (oddReg R 9) &&
    oddPerfOK #[oddReg R 9, oddReg R 14] Data.oddPerfY (oddReg R 14)

@[expose] def oddX : Array Nat := oddReg oddBRegs 9

@[expose] def oddY : Array Nat := oddReg oddBRegs 14

@[expose] def oddHs (x y : Array Nat) : Array (Array Nat) :=
  (Data.oddHWords.map (lineRows #[x, y])).toArray

@[expose] def oddUs (Hs : Array (Array Nat)) (u0 u1 : Nat) : Array Nat :=
  Array.ofFn (n := 24) fun i =>
    vecMulN 24 (transposeRows 24 Hs[i.val]!) (if Data.oddSel.getD i.val 0 = 0 then u0 else u1)

@[expose] def oddHsB : Array (Array Nat) := oddHs oddX oddY

@[expose] def oddBT : Array Nat := oddUs oddHsB (Data.oddSeeds.getD 0 0) (Data.oddSeeds.getD 1 0)

@[expose] def oddCandOK (x y s : Array Nat) (Hs : Array (Array Nat)) (BT BTi : Array Nat)
    (u0 u1 : Nat) : Bool :=
  let Us := oddUs Hs u0 u1
  let T := transposeRows 24 (mulRows 24 BTi Us)
  (List.range 24).all (fun i => vecMulN 24 (transposeRows 24 T) BT[i]! == Us[i]!) &&
    (!(mulRows 24 T x == mulRows 24 x T && mulRows 24 T y == mulRows 24 y T &&
        mulRows 24 T s == mulRows 24 s T && T != idRows 24) ||
      [3, 5, 7, 13].all fun p => powRows 24 T p != idRows 24)

@[expose] def oddCandCheckOf (x y s : Array Nat) (Hs : Array (Array Nat)) (BT BTi : Array Nat)
    (L : List Nat) : Bool :=
  L.all fun u0 => L.all fun u1 => oddCandOK x y s Hs BT BTi u0 u1

end Native

end CFSG.Sporadic.Co1Schreier
