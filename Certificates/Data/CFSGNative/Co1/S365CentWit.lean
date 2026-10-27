module

public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import Certificates.Data.CFSGNative.Co1.S365CentRoot

public section

namespace CFSG.Sporadic.Co1.S365CentNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native

@[expose] def collectLt (p : Nat → Bool) : Nat → List Nat → List Nat
  | 0, acc => acc
  | n + 1, acc => collectLt p n (if p n then n :: acc else acc)

@[expose] def pat0 (qr pts : Array Nat) (pos : Array UInt32) (n x y om v : Nat) : Bool :=
  tyLabN qr pts pos n v == 1 && tyLabN qr pts pos n (v ^^^ x) == 3 &&
    tyLabN qr pts pos n (v ^^^ y) == 3 && tyLabN qr pts pos n (v ^^^ x ^^^ y) == 3 &&
    tyLabN qr pts pos n (v ^^^ om) == 1 && tyLabN qr pts pos n (v ^^^ om ^^^ x) == 1 &&
    tyLabN qr pts pos n (v ^^^ om ^^^ y) == 1 && tyLabN qr pts pos n (v ^^^ om ^^^ x ^^^ y) == 1

@[expose] def killed (qr pts : Array Nat) (pos : Array UInt32) (n x y om : Nat)
    (Mts : Array (Array Nat)) (path : List Nat) (v : Nat) : Bool :=
  decide (v ^^^ applyPath Mts path v < 16777216) && (v ^^^ applyPath Mts path v) != 0 &&
    !pat0 qr pts pos n x y om (v ^^^ applyPath Mts path v)

@[expose] def witCheck (qr pts : Array Nat) (pos : Array UInt32) (n x y om : Nat)
    (Mts : Array (Array Nat)) (pA pB : List Nat) : Bool :=
  applyPath Mts pA om == om && applyPath Mts pB om == om &&
    countBelow (fun v => pat0 qr pts pos n x y om v && v != 1 &&
      !(killed qr pts pos n x y om Mts pA v || killed qr pts pos n x y om Mts pB v))
      16777216 0 == 0

@[expose] def noPat (qr pts : Array Nat) (pos : Array UInt32) (n : Nat) (gs : List Nat) : Bool :=
  let L := collectLt (orthAllN gs) 16777216 []
  L.all fun a => tyLabN qr pts pos n a != 3 ||
    L.all fun b => tyLabN qr pts pos n b != 3 || tyLabN qr pts pos n (a ^^^ b) != 3 ||
      L.all fun om => !(tyLabN qr pts pos n om == 1 && tyLabN qr pts pos n (om ^^^ a) == 1 &&
        tyLabN qr pts pos n (om ^^^ b) == 1 && tyLabN qr pts pos n (om ^^^ a ^^^ b) == 1)

end CFSG.Sporadic.Co1.S365CentNative
