module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

@[expose] def octItem (o : Nat) : Bool := decide (o < 2 ^ 24) && Native.pop o == 8 && Native.synd o == 0

@[expose] def trioItem (t : Nat × Nat × Nat) : Bool :=
  decide (t.1 < t.2.1) && decide (t.2.1 < t.2.2) &&
    t.1 &&& t.2.1 == 0 && t.1 &&& t.2.2 == 0 && t.2.1 &&& t.2.2 == 0 &&
    (t.1 ||| t.2.1 ||| t.2.2) == Native.full

@[expose] def sextItem (s : List Nat) : Bool :=
  s.length == 6 && sortN s == s && decide (s.Pairwise (· < ·)) &&
    s.all (fun B => Native.pop B == 4 && decide (B < 2 ^ 24)) &&
    s.foldl (· ||| ·) 0 == Native.full &&
    s.all fun B => s.all fun B' => B == B' || B &&& B' == 0

@[expose] def pairsOK (O : List Nat) (posT : KTree (Nat × Nat)) : Bool :=
  O.all fun a => O.all fun b =>
    a &&& b != 0 || a == b ||
      decide (idxK posT Native.nTrio (Native.key3 (Native.sort3 a b (Native.full ^^^ a ^^^ b))) <
        Native.nTrio)

@[expose] def disjCount (O : List Nat) : Nat :=
  (O.map fun a => (O.filter fun b => a &&& b == 0 && a != b).length).sum

@[expose] def tetOK (O : List Nat) (posS : KTree (Nat × Nat)) (t : Nat) : Bool :=
  (O.filter (fun o => o &&& t == t)).length == 5 &&
    decide (idxK posS Native.nSext
      (Native.keyL (sortN (t :: (O.filter (fun o => o &&& t == t)).map (· ^^^ t)))) < Native.nSext)

@[expose] def pair0 (a : Nat) : Nat := 1 ||| (1 <<< a)

@[expose] def tetsA (a : Nat) : List Nat :=
  (List.range 24).flatMap fun b => (List.range 24).filterMap
    fun c => if 0 < a && a < b && b < c then some (1 ||| (1 <<< a) ||| (1 <<< b) ||| (1 <<< c))
      else none

@[expose] def tetsOK (O : List Nat) (posS : KTree (Nat × Nat)) : Bool :=
  (List.range 24).all fun a =>
    (tetsA a).all fun t => decide (t < 2 ^ 24) && t &&& pair0 a == pair0 a &&
      tetOK (O.filter fun o => o &&& pair0 a == pair0 a) posS t

@[expose] def baseOK (posO : KTree (Nat × Nat)) : Bool :=
  [Native.baseTrio.1, Native.baseTrio.2.1, Native.baseTrio.2.2].all
      (fun o => decide (idxK posO Native.nOct o < Native.nOct)) &&
    Native.baseSext.all fun B => Native.baseSext.all fun B' =>
      B == B' || decide (idxK posO Native.nOct (B ||| B') < Native.nOct)

end CFSG.KC.M24G
