module

public import Certificates.Data.D4HexBase
public import Certificates.Data.D4HexOrb
public import Certificates.Data.D4HexF48Words

public section

namespace CFSG.D4Hex

open CFSG.Monster.B.Co2.Native

@[expose] def f48EvalW (G : Array (Array Nat)) : List Nat → Array Nat
  | [] => idA 819
  | l :: w => compA 819 G[l]! (f48EvalW G w)

@[expose] def f48WordArrs (G : Array (Array Nat)) (ws : List (List Nat)) : Array (Array Nat) :=
  (ws.map (f48EvalW G)).toArray

@[expose] def f48LettersOK (k : Nat) (ws : List (List Nat)) : Bool :=
  ws.all fun w => w.all fun l => decide (l < k)

@[expose] def f48PowLoop : Nat → Array Nat → Nat → Array Nat → Array Nat
  | 0, _, _, r => r
  | fuel + 1, b, e, r =>
    if e == 0 then r
    else f48PowLoop fuel (compA 819 b b) (e / 2) (if e % 2 == 1 then compA 819 b r else r)

@[expose] def f48PowA (b : Array Nat) (e : Nat) : Array Nat := f48PowLoop 40 b e (idA 819)

@[expose] def f48OnL0 (x : Nat) : Bool := x == 0 || x == 1 || x == 5

@[expose] def f48MapsL0 (a : Array Nat) : Bool := f48OnL0 a[0]! && f48OnL0 a[1]! && f48OnL0 a[5]!

@[expose] def f48InB (a : Array Nat) : Bool := a[0]! == 0 && f48MapsL0 a

@[expose] def f48NOK (n : Array Nat) : Bool :=
  eqA 819 (compA 819 n n) (idA 819) && n[0]! == 0 && !f48MapsL0 n

@[expose] def f48Conj (n f : Array Nat) : Array Nat := compA 819 n (compA 819 f n)

@[expose] def f48FOK (n : Array Nat) (F : Array (Array Nat)) : Bool :=
  allLt F.size fun j => f48InB F[j]! && f48InB (f48Conj n F[j]!)

@[expose] def f48BsOK (bs : Array (Array Nat)) : Bool :=
  decide (bs.size = 8) && allLt bs.size fun j => f48InB bs[j]!

@[expose] def f48LayOK (lay : Array Nat) (p0 : Nat) : Bool :=
  lay[p0]! == 6 && allLt 819 fun x => decide (lay[x]! ≤ 4) || lay[x]! == 6

@[expose] def f48Rec (F : Array (Array Nat)) (p0 : Nat) : OrbRec :=
  orbBFS 819 F.size (fun j x => F[j]![x]!) p0

@[expose] def f48OrbOK (lay : Array Nat) (F : Array (Array Nat)) (r : OrbRec) (p0 : Nat) : Bool :=
  orbOK 819 F.size (fun j x => F[j]![x]!) p0 512 (fun x => lay[x]! == 6) r

@[expose] def f48TArr (F : Array (Array Nat)) (r : OrbRec) (p0 k : Nat) : Array Nat := Id.run do
  let mut a := (idA 819).set! p0 k
  for i in [1:512] do
    a := a.set! r.ord[i]! ((F[r.lab[i]!]!)[a[r.ord[r.par[i]!]!]!]!)
  return a

@[expose] def f48CandOK (lay : Array Nat) (F : Array (Array Nat)) (r : OrbRec) (p0 : Nat)
    (a : Array Nat) (k : Nat) : Bool :=
  a[p0]! == k && (allLt 819 fun p => decide (4 < lay[p]!) || a[p]! == p) &&
    allLt 512 fun i => i == 0 || a[r.ord[i]!]! == (F[r.lab[i]!]!)[a[r.ord[r.par[i]!]!]!]!

@[expose] def f48FullFail (M : Nat) (n q a : Array Nat) : Bool :=
  let m := compA 819 n a
  !eqA 819 (compA 819 m m) (idA 819) || !eqA 819 (f48PowA (compA 819 m q) M) (idA 819)

@[expose] def f48KeyOK (lay : Array Nat) (F : Array (Array Nat)) (r : OrbRec) (M p0 : Nat)
    (n q : Array Nat) (k : Nat) : Bool :=
  let a := f48TArr F r p0 k
  f48CandOK lay F r p0 a k &&
    if k == p0 then eqA 819 a (idA 819) else f48FullFail M n q a

@[expose] def f48KeyAll (lay : Array Nat) (F : Array (Array Nat)) (r : OrbRec) (M p0 : Nat)
    (n q : Array Nat) : Bool :=
  allLt 819 fun k => !(lay[k]! == 6) || f48KeyOK lay F r M p0 n q k

@[expose] def f48LinePt (lineTab : Array Nat) (l j : Nat) : Nat := lineTab[3 * l + j]!

@[expose] def f48LineHas0 (lineTab : Array Nat) (l : Nat) : Bool :=
  f48LinePt lineTab l 0 == 0 || f48LinePt lineTab l 1 == 0 || f48LinePt lineTab l 2 == 0

@[expose] def f48In3 (x a b c : Nat) : Bool := x == a || x == b || x == c

@[expose] def f48LineIn (lineTab : Array Nat) (l a b c : Nat) : Bool :=
  f48In3 (f48LinePt lineTab l 0) a b c && f48In3 (f48LinePt lineTab l 1) a b c &&
    f48In3 (f48LinePt lineTab l 2) a b c

@[expose] def f48LineInImg (lineTab : Array Nat) (l : Nat) (a : Array Nat) : Bool :=
  f48LineIn lineTab l a[0]! a[1]! a[5]!

@[expose] def f48LinesOK (lineTab : Array Nat) (n : Array Nat) (bs : Array (Array Nat)) : Bool :=
  allLt 2457 fun l => !f48LineHas0 lineTab l || f48LineIn lineTab l 0 1 5 ||
    (List.range 8).any fun j => f48LineInImg lineTab l (compA 819 bs[j]! n)

@[expose] def f48FixOK (F : Array (Array Nat)) : Bool :=
  allLt 819 fun x => x == 0 || !(allLt F.size fun j => F[j]![x]! == x)

@[expose] def hexF48Check (M p0 : Nat) (nW qW : List Nat) (fW bW : List (List Nat))
    (lineTab lay : Array Nat) (G : Array (Array Nat)) : Bool :=
  let n := f48EvalW G nW
  let q := f48EvalW G qW
  let F := f48WordArrs G fW
  let bs := f48WordArrs G bW
  let r := f48Rec F p0
  decide (M < 2 ^ 40) && f48LettersOK G.size ([nW, qW] ++ fW ++ bW) && f48NOK n &&
    f48MapsL0 q && f48FOK n F && f48BsOK bs && f48LayOK lay p0 && f48OrbOK lay F r p0 &&
    f48KeyAll lay F r M p0 n q && f48LinesOK lineTab n bs && f48FixOK F

end CFSG.D4Hex
