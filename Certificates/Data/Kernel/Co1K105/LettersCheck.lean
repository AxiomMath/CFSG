module

public import Certificates.Data.CFSGNative.Co1.CoverCheck
public import Certificates.Data.CFSGNative.Co1Schreier.Base

public section

namespace CFSG.KD.Co1K105

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.InvNative

@[expose] def qElt (e a : Rows) (qs : List Rows) (i : Nat) : Rows :=
  let x := (List.range 8).foldl (fun x j => if i.testBit j then mul x (qs.getD j e) else x) e
  if i.testBit 8 then mul x a else x

@[expose] def wordRows (e x y : Rows) (w : List Bool) : Rows :=
  w.foldl (fun acc b => mul acc (if b then y else x)) e

@[expose] def qTableOK (e : Rows) (Q : Array Rows) (qs : List Rows) : Bool :=
  (List.range 512).all (fun i => validRows Q[i]! && (List.range i).all fun j => Q[i]! != Q[j]!) &&
    (List.range 8).all fun j => Q[2 ^ j]! == qs.getD j e

@[expose] def letterOK (e : Rows) (Q : Array Rows) (L : Nat → Nat → Nat) (l : Nat) (g : Rows) :
    Bool :=
  let gi := inv g
  mul g gi == e && (List.range 512).all fun i =>
    let j := L l i
    decide (j < 512) && mul (mul g Q[i]!) gi == Q[j]!

@[expose] def co1KLettersCheck (A x y a : Rows) (eps : Array Rows) (qs bray : List Rows)
    (ws : List (List Bool)) (L : Nat → Nat → Nat) : Bool :=
  let e := one
  let Ai := inv A
  let z := eprodRows eps 3
  let c := mul (pow (mul (mul (mul A z) Ai) a) 2) A
  let ci := inv c
  let Q := (Array.range 512).map (qElt e a qs)
  mul A Ai == e && mul c ci == e && mul (mul c z) ci == a && qTableOK e Q qs &&
    (List.range 11).all (fun i => letterOK e Q L i (mul (mul c eps[i]!) ci)) &&
    (List.range 4).all (fun j =>
      letterOK e Q L (11 + j) (mul (mul c (wordRows e x y (ws.getD j []))) ci)) &&
    letterOK e Q L 15 (mul (mul (bray.getD 0 e) (bray.getD 7 e)) (bray.getD 4 e)) &&
    letterOK e Q L 16 (bray.getD 0 e)

end CFSG.KD.Co1K105

end
