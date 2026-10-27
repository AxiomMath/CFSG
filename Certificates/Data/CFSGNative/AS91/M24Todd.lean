module

public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def ccEColsN : List Nat :=
  [30, 65, 33, 97, 29, 258, 130, 386, 27, 1028, 516, 1540, 23, 1352, 680, 2024, 15, 1456, 880,
    1744, 31, 1248, 960, 1824]

@[expose] def liftEColsN : List Nat :=
  [0x100001, 0x100010, 0x100100, 0x101000, 0x110000, 0x6ca000, 0xa6c000, 0xc6a000, 0x6ac000,
    0xaaa000, 0xccc000]

@[expose] def toddPopc : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => a % 2 + toddPopc k (a / 2)

@[expose] def toddEven (k a : Nat) : Bool := toddPopc k a % 2 == 0

@[expose] def toddAct (a : Array Nat) (m : Nat) : Nat :=
  actM ccEColsN (img a (actM liftEColsN m))

@[expose] def toddOct (o w : Nat) : Bool := toddEven 24 (o &&& actM liftEColsN w)

@[expose] def toddOrth (u w : Nat) : Bool := toddEven 11 (u &&& w)

@[expose] def toddOctsKer (os : List Nat) (w : Nat) : Bool := os.all fun o => toddOct o w

@[expose] def toddActTabs (_ : Unit := ()) : List (Array Nat) :=
  lTabs.map fun a => (Array.range 2048).map (toddAct a)

@[expose] def toddKerT (tabs : List (Array Nat)) (u w : Nat) : Bool :=
  toddOrth u w && tabs.all fun T => toddOrth u T[w]!

@[noinline, expose] def toddUniqRow (tabs : List (Array Nat)) (br : List Nat) (u : Nat) : Bool :=
  decide (((List.range 2048).filter (toddKerT tabs u)).length < 512) ||
    (List.range 2048).all fun w => !(toddKerT tabs u w) || toddOctsKer br w

@[noinline, expose] def toddUniqLoop (tabs : List (Array Nat)) (br : List Nat) : Bool :=
  (List.range 2048).all fun u => u == 0 || toddUniqRow tabs br u

@[expose] def toddUniqCheck (_ : Unit := ()) : Bool :=
  toddUniqLoop (toddActTabs ()) (octsT baseTrio)

@[expose] def toddInterCount (T : Array (Nat × Nat × Nat)) (K0 : List Nat) (k : Nat) : Nat :=
  (K0.filter (toddOctsKer (octsT T[k]!))).length

@[noinline, expose] def toddIntReps (T : Array (Nat × Nat × Nat)) (S : Array (List Nat))
    (K0 : List Nat) : Bool :=
  meets T[0]! T[267]! && toddInterCount T K0 267 == 256 &&
    !(meets T[0]! T[23]!) && trioIn T[0]! S[1293]! && trioIn T[23]! S[1293]! &&
      toddInterCount T K0 23 == 128 &&
    zc T[0]! T[22]! == 1 && toddInterCount T K0 22 == 128 &&
    zc T[0]! T[1]! == 0 && toddInterCount T K0 1 == 128

@[expose] def toddIntCheck (_ : Unit := ()) : Bool :=
  let T := trioList ()
  let S := sextList ()
  let K0 := (List.range 2048).filter (toddOctsKer (octsT baseTrio))
  K0.length == 512 && toddIntReps T S K0

@[noinline, expose] def toddSextLoop (K0 : List Nat) (S : Array (List Nat)) : Bool :=
  allLt nSext fun q => q == 0 || (let os := octsS S[q]!
    K0.any fun w => !(toddOctsKer os w))

@[expose] def toddSextCheck (_ : Unit := ()) : Bool :=
  let S := sextList ()
  let K0 := (List.range 2048).filter (toddOctsKer (octsS S[0]!))
  K0.length == 128 && toddSextLoop K0 S

@[expose] def toddCheck (_ : Unit := ()) : Bool :=
  toddUniqCheck () && toddIntCheck () && toddSextCheck ()

end CFSG.Quasithin.H13.AS91.M24G.Native
